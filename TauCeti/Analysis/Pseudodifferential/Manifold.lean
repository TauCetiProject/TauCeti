/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.ChartCompression
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow

/-!
# Classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. A complex-linear operator `P` on the complex-valued smooth
functions on `M` is read in a chart `e` of the maximal smooth atlas through two cutoffs `φ` and `ψ`
with compact supports in the chart target: its chart compression is the operator

`u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹`

on functions on `ℝⁿ` (`OpenPartialHomeomorph.complexChartCompression`). Following Hörmander
(III, Definition 18.1.20, for properly supported operators), `P` is a **classical
pseudodifferential operator of order `m`** when it is properly supported and every such
compression, for every chart and every pair of cutoffs, is the left quantization `Op(a)` of a
classical symbol `a` of order `m` on Schwartz functions
(`TauCeti.classicalPseudodifferentialOperators`). No smoothing remainder needs to be added
separately: a smoothing symbol is a classical symbol of every order
(`TauCeti.ClassicalSymbol.ofIsSmoothing`), so the operators `Op(a) + Op(r)` with `r` smoothing are
already of this form.

The charts range over the whole maximal atlas, which also contains the charts whose domain is a
disjoint union of two small coordinate balls mapped to disjoint balls of `ℝⁿ`; on such a chart,
cutoffs with disjoint supports in the two balls see the part of `P` between two distant points.
So the condition also controls `P` off the diagonal, which is why it is imposed in every chart
and not only in the charts of a fixed atlas.

The chart compressions only apply `P` to compactly supported functions. The operators here are
defined on all smooth functions, so the class also asks `P` to be properly supported: for every
compact set `K` there is a compact set `K'` such that `P` sends functions supported in `K` to
functions supported in `K'`, and `P f` vanishes on `K` whenever `f` vanishes near `K'`. The second
condition makes `P f` on `K` depend only on `f` near `K'`. On a smooth manifold, multiplying `f`
by a compactly supported cutoff equal to `1` near `K'` then shows that `P` is determined by its
values on compactly supported functions, and hence by its chart compressions.

## Main results

* `TauCeti.classicalPseudodifferentialOperators m`: the properly supported operators all of whose
  chart compressions are quantizations of classical symbols of order `m`, a complex submodule of
  the operators on `C^∞(M, ℂ)`.
* `TauCeti.classicalPseudodifferentialOperators_le`: an operator of order `m - k`, `k ∈ ℕ`, has
  order `m`.
* `TauCeti.id_mem_classicalPseudodifferentialOperators` and
  `TauCeti.mulLeft_mem_classicalPseudodifferentialOperators`: the identity and multiplication by a
  smooth function have order `0`.
* `TauCeti.mulLeft_comp_mem_classicalPseudodifferentialOperators` and
  `TauCeti.comp_mulLeft_mem_classicalPseudodifferentialOperators`: multiplying an operator of order
  `m` by a smooth function, on either side, gives an operator of order `m`.
* `TauCeti.complexifyLinearMap_mem_classicalPseudodifferentialOperators`: the complexification of a
  differential operator of order at most `m` on the real-valued smooth functions on `M`, in
  Grothendieck's sense, is a classical pseudodifferential operator of order `m`. Its symbol in a
  chart is the polynomial symbol of the compression
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_chartCompression`), with
  no smoothing remainder.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Definition
  18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]

/-- The **classical pseudodifferential operators of order `m`** on a manifold `M` modelled on
`ℝⁿ`: the complex-linear operators `P` on the complex-valued smooth functions on `M` such that

* `P` is properly supported: for every compact set `K` there is a compact set `K'` such that
  `P f` is supported in `K'` whenever `f` is supported in `K`, and `P f` vanishes on `K`
  whenever `f` vanishes on a neighbourhood of `K'`;
* for every chart `e` of the maximal smooth atlas and all cutoffs `φ`, `ψ` with compact supports
  in the chart target, the chart compression `u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` agrees on Schwartz
  functions with the quantization `Op(a)` of a classical symbol `a` of order `m`. -/
def classicalPseudodifferentialOperators (m : ℝ) :
    Submodule ℂ (C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) where
  carrier := {P | (∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
      (∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        tsupport f ⊆ K → tsupport (P f) ⊆ K') ∧
        ∀ f, (∀ᶠ y in 𝓝ˢ K', f y = 0) → ∀ x ∈ K, P f x = 0) ∧
    ∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
      (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)), ∃ a : ClassicalSymbol n ℂ ℂ m,
        ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
          quantizeSchwartzValue a.toSymbol.coefficient u x =
            e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x}
  zero_mem' := ⟨fun K hK ↦ ⟨K, hK, by simp, by simp⟩, fun _ _ _ _ ↦ ⟨0, fun u x ↦ by
    simp [ClassicalSymbol.toSymbol_zero, Symbol.coefficient_zero]⟩⟩
  add_mem' {P Q} hP hQ := by
    refine ⟨fun K hK ↦ ?_, fun e he φ ψ ↦ ?_⟩
    · obtain ⟨K₁, hK₁, hP₁, hP₂⟩ := hP.1 K hK
      obtain ⟨K₂, hK₂, hQ₁, hQ₂⟩ := hQ.1 K hK
      refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
      · rw [LinearMap.add_apply, ContMDiffMap.coe_add]
        exact (tsupport_add _ _).trans (union_subset_union (hP₁ f hf) (hQ₁ f hf))
      · rw [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply,
          hP₂ f (hf.filter_mono (nhdsSet_mono subset_union_left)) x hx,
          hQ₂ f (hf.filter_mono (nhdsSet_mono subset_union_right)) x hx, add_zero]
    obtain ⟨a, ha⟩ := hP.2 e he φ ψ
    obtain ⟨b, hb⟩ := hQ.2 e he φ ψ
    refine ⟨a + b, fun u x ↦ ?_⟩
    rw [ClassicalSymbol.toSymbol_add, Symbol.coefficient_add,
      Symbol.quantizeSchwartzValue_coefficient_add, ha, hb]
    simp
  smul_mem' c P hP := by
    refine ⟨fun K hK ↦ ?_, fun e he φ ψ ↦ ?_⟩
    · obtain ⟨K', hK', hP₁, hP₂⟩ := hP.1 K hK
      refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
      · refine (closure_mono (Function.support_subset_iff'.2 fun x hx ↦ ?_)).trans (hP₁ f hf)
        simp [ContMDiffMap.complex_smul_apply, Function.notMem_support.1 hx]
      · simp [ContMDiffMap.complex_smul_apply, hP₂ f hf x hx]
    obtain ⟨a, ha⟩ := hP.2 e he φ ψ
    refine ⟨c • a, fun u x ↦ ?_⟩
    rw [ClassicalSymbol.toSymbol_smul, Symbol.coefficient_smul, quantizeSchwartzValue_smul_left,
      ha]
    simp

theorem mem_classicalPseudodifferentialOperators_iff {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} :
    P ∈ classicalPseudodifferentialOperators m ↔
      (∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
        (∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
          tsupport f ⊆ K → tsupport (P f) ⊆ K') ∧
          ∀ f, (∀ᶠ y in 𝓝ˢ K', f y = 0) → ∀ x ∈ K, P f x = 0) ∧
      ∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
        (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
        (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)), ∃ a : ClassicalSymbol n ℂ ℂ m,
          ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
            quantizeSchwartzValue a.toSymbol.coefficient u x =
              e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x :=
  Iff.rfl

/-- **Inclusion of orders.** A classical pseudodifferential operator of order `m' = m - k`,
`k ∈ ℕ`, has order `m`. As for classical symbols (`TauCeti.ClassicalSymbol.inclusion`), orders
with a non-integer difference are not comparable. -/
theorem classicalPseudodifferentialOperators_le {m m' : ℝ} (k : ℕ) (hk : m' = m - k) :
    classicalPseudodifferentialOperators (n := n) (M := M) m' ≤
      classicalPseudodifferentialOperators m :=
  fun _ hP ↦ mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1, fun e he φ ψ ↦
    let ⟨a, ha⟩ := hP.2 e he φ ψ
    ⟨ClassicalSymbol.inclusion k hk a, fun u x ↦ by
      rw [ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion, ha]⟩⟩

/-! ### Multiplication operators -/

section Multiplication

/-- **The identity is a classical pseudodifferential operator of order `0`.** In a chart, its
compression by `φ` and `ψ` is multiplication by `φ ψ`, the quantization of the symbol `φ(x) ψ(x)`
of order `0`. -/
theorem id_mem_classicalPseudodifferentialOperators :
    LinearMap.id ∈ classicalPseudodifferentialOperators (n := n) (M := M) 0 := by
  refine mem_classicalPseudodifferentialOperators_iff.2
    ⟨fun K hK ↦ ⟨K, hK, fun f hf ↦ hf, fun f hf x hx ↦ hf.self_of_nhdsSet x hx⟩,
      fun e he φ ψ ↦ ?_⟩
  have hφψ : ContDiff ℝ ∞ fun y ↦ ((φ y * ψ y : ℝ) : ℂ) • ContinuousLinearMap.id ℂ ℂ :=
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.mul ψ.contDiff)).smul contDiff_const
  refine ⟨ClassicalSymbol.ofSpatial _ hφψ, fun u x ↦ ?_⟩
  rw [ClassicalSymbol.toSymbol_ofSpatial, Symbol.quantizeSchwartzValue_ofSpatial,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.id_apply]
  by_cases hφ : φ x = 0
  · simp [hφ]
  · have hx : x ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
    rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hx),
      e.right_inv hx]
    simp [Complex.real_smul, mul_assoc]

/-- **Multiplication on the left.** If `P` is a classical pseudodifferential operator of order
`m`, then so is `u ↦ g · P u` for every complex-valued smooth function `g`. In a chart, the
compression of `g P` by `φ` and `ψ` is the sum of the compressions of `P` by `φ (Re g)` and `ψ`,
and by `φ (Im g)` and `ψ` times `i`, where `g` is read in the chart. -/
theorem mulLeft_comp_mem_classicalPseudodifferentialOperators {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    LinearMap.mulLeft ℂ g ∘ₗ P ∈ classicalPseudodifferentialOperators m := by
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨fun K hK ↦ ?_, fun e he φ ψ ↦ ?_⟩
  · obtain ⟨K', hK', hP₁, hP₂⟩ := hP.1 K hK
    refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
      exact tsupport_mul_subset_right.trans (hP₁ f hf)
    · simp [hP₂ f hf x hx]
  have hg : ContDiffOn ℝ ∞ (fun y ↦ g (e.symm y)) e.target := contMDiffOn_iff_contDiffOn.1
    (g.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he))
  obtain ⟨a₁, ha₁⟩ := hP.2 e he
    (TestFunction.smulLeftCLMOfContDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hg) φ) ψ
  obtain ⟨a₂, ha₂⟩ := hP.2 e he
    (TestFunction.smulLeftCLMOfContDiffOn (Complex.imCLM.contDiff.comp_contDiffOn hg) φ) ψ
  refine ⟨a₁ + Complex.I • a₂, fun u x ↦ ?_⟩
  rw [ClassicalSymbol.toSymbol_add, Symbol.coefficient_add,
    Symbol.quantizeSchwartzValue_coefficient_add, ClassicalSymbol.toSymbol_smul,
    Symbol.coefficient_smul, quantizeSchwartzValue_smul_left, ha₁, ha₂]
  simp only [OpenPartialHomeomorph.complexChartCompression_apply,
    TestFunction.smulLeftCLMOfContDiffOn_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ContMDiffMap.coe_mul, Pi.mul_apply, Function.comp_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im (g (e.symm x))]
  push_cast
  ring

/-- **Multiplication on the right.** If `P` is a classical pseudodifferential operator of order
`m`, then so is `u ↦ P (g u)` for every complex-valued smooth function `g`. In a chart, the
compression of `P g` by `φ` and `ψ` is the sum of the compressions of `P` by `φ` and `ψ (Re g)`,
and by `φ` and `ψ (Im g)` times `i`, where `g` is read in the chart. -/
theorem comp_mulLeft_mem_classicalPseudodifferentialOperators {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    P ∘ₗ LinearMap.mulLeft ℂ g ∈ classicalPseudodifferentialOperators m := by
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨fun K hK ↦ ?_, fun e he φ ψ ↦ ?_⟩
  · obtain ⟨K', hK', hP₁, hP₂⟩ := hP.1 K hK
    refine ⟨K', hK', fun f hf ↦ hP₁ _ ?_, fun f hf ↦ hP₂ _ (hf.mono fun y hy ↦ ?_)⟩
    · rw [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
      exact tsupport_mul_subset_right.trans hf
    · simp [hy]
  have hg : ContDiffOn ℝ ∞ (fun y ↦ g (e.symm y)) e.target := contMDiffOn_iff_contDiffOn.1
    (g.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he))
  set ψ₁ := TestFunction.smulLeftCLMOfContDiffOn (Complex.reCLM.contDiff.comp_contDiffOn hg) ψ
  set ψ₂ := TestFunction.smulLeftCLMOfContDiffOn (Complex.imCLM.contDiff.comp_contDiffOn hg) ψ
  obtain ⟨a₁, ha₁⟩ := hP.2 e he φ ψ₁
  obtain ⟨a₂, ha₂⟩ := hP.2 e he φ ψ₂
  refine ⟨a₁ + Complex.I • a₂, fun u x ↦ ?_⟩
  -- On the manifold, `g` times the pullback by `ψ` is the pullback by `ψ (Re g)` plus `i` times
  -- the pullback by `ψ (Im g)`.
  have key (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯) :
      g * e.complexCutoffPullback he ψ f =
        e.complexCutoffPullback he ψ₁ f + Complex.I • e.complexCutoffPullback he ψ₂ f := by
    ext y
    by_cases hy : y ∈ e.source
    · simp only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_add, Pi.add_apply,
        ContMDiffMap.complex_smul_apply,
        OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hy, ψ₁, ψ₂,
        TestFunction.smulLeftCLMOfContDiffOn_apply, e.left_inv hy, Function.comp_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im (g y)]
      push_cast
      ring_nf
    · simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hy]
  rw [ClassicalSymbol.toSymbol_add, Symbol.coefficient_add,
    Symbol.quantizeSchwartzValue_coefficient_add, ClassicalSymbol.toSymbol_smul,
    Symbol.coefficient_smul, quantizeSchwartzValue_smul_left, ha₁, ha₂]
  simp only [OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, key, map_add, map_smul, ContMDiffMap.coe_add, Pi.add_apply,
    ContMDiffMap.complex_smul_apply, smul_add, smul_eq_mul, Complex.real_smul]
  ring

/-- **Multiplication by a smooth function is a classical pseudodifferential operator of order
`0`.** -/
theorem mulLeft_mem_classicalPseudodifferentialOperators
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    LinearMap.mulLeft ℂ g ∈ classicalPseudodifferentialOperators (n := n) (M := M) 0 := by
  simpa using mulLeft_comp_mem_classicalPseudodifferentialOperators
    id_mem_classicalPseudodifferentialOperators g

end Multiplication

/-! ### Differential operators -/

/-- **Differential operators are classical pseudodifferential operators.** The complexification of
a differential operator `D` of order at most `m` on the real-valued smooth functions on `M`, in
Grothendieck's sense of iterated commutators with multiplication operators, is a classical
pseudodifferential operator of order `m`. In a chart, its compression is exactly the quantization
of the polynomial symbol of the compression of `D`
(`TauCeti.ClassicalSymbol.ofDifferentialOperator`), whose principal symbol is read from the
geometric principal symbol of `D`
(`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialOperator_chartCompression`). -/
theorem complexifyLinearMap_mem_classicalPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m) :
    ContMDiffMap.complexifyLinearMap D ∈
      classicalPseudodifferentialOperators (n := n) (M := M) m := by
  -- Like `D`, its complexification is local, so it is properly supported with `K' = K`.
  have hloc (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M)
      (hf : ∀ᶠ y in 𝓝 x, f y = 0) : ContMDiffMap.complexifyLinearMap D f x = 0 := by
    have hD₀ (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hg : ∀ᶠ y in 𝓝 x, g y = 0) :
        D g x = 0 := by
      simpa using differentialOperators_apply_eq_of_eventuallyEq hD (g := 0) hg
    simp [ContMDiffMap.complex_smul_apply, ContMDiffMap.ofReal_apply,
      hD₀ (ContMDiffMap.re f) (hf.mono fun y hy ↦ by simp [ContMDiffMap.re_apply, hy]),
      hD₀ (ContMDiffMap.im f) (hf.mono fun y hy ↦ by simp [ContMDiffMap.im_apply, hy])]
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨fun K hK ↦ ⟨K, hK, fun f hf ↦ ?_,
    fun f hf x hx ↦ hloc f x (hf.filter_mono (nhds_le_nhdsSet hx))⟩, fun e he φ ψ ↦ ?_⟩
  · refine (closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport f)).trans hf
    by_contra h
    exact hx (hloc f x (notMem_tsupport_iff_eventuallyEq.1 h))
  refine ⟨ClassicalSymbol.ofDifferentialOperator ℂ
    (e.chartCompressionDifferentialOperators he φ ψ m ⟨D, hD⟩), fun u x ↦ ?_⟩
  rw [ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_chartCompression]
  -- The real and imaginary parts of `u` as smooth functions, in the form in which they enter
  -- the compression of `D`; both sides evaluate to `(u y).re` (resp. `(u y).im`).
  have hre : (ContMDiffMap.ofContDiff u (u.smooth ⊤) :
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯).re =
      ⟨fun y ↦ (u y).re, (Complex.reCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩ := by
    ext y
    simp only [ContMDiffMap.re_apply, ContMDiffMap.coe_ofContDiff]
    rfl
  have him : (ContMDiffMap.ofContDiff u (u.smooth ⊤) :
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯).im =
      ⟨fun y ↦ (u y).im, (Complex.imCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩ := by
    ext y
    simp only [ContMDiffMap.im_apply, ContMDiffMap.coe_ofContDiff]
    rfl
  simp only [hre, him, OpenPartialHomeomorph.complexChartCompression_apply,
    ContMDiffMap.complexifyLinearMap_apply, OpenPartialHomeomorph.complexCutoffPullback_re,
    OpenPartialHomeomorph.complexCutoffPullback_im, ContMDiffMap.coe_add, Pi.add_apply,
    ContMDiffMap.complex_smul_apply, ContMDiffMap.ofReal_apply, Complex.real_smul]
  ring

end TauCeti
