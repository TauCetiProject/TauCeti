/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.ChartCompression
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.LocallyFiniteSum
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

* `TauCeti.IsProperlySupported P`: the operator `P` is properly supported. The identity, sums,
  scalar multiples, products with smooth functions on either side and local operators
  (`TauCeti.IsProperlySupported.of_local`) are properly supported.
* `TauCeti.isProperlySupported_locallyFiniteSum`: the locally finite sum
  `ContMDiffMap.locallyFiniteSum P hP` of operators `f ↦ ∑ᵢ Pᵢ f` is properly supported when the
  outputs of `Pᵢ` lie in compact sets `Sᵢ` forming a locally finite family and each `Pᵢ` only sees
  its input near `Sᵢ`.
* `TauCeti.classicalPseudodifferentialOperators m`: the properly supported operators all of whose
  chart compressions are quantizations of classical symbols of order `m`, a complex submodule of
  the operators on `C^∞(M, ℂ)`.
* `TauCeti.classicalPseudodifferentialOperators_le`: an operator of order `m - k`, `k ∈ ℕ`, has
  order `m`.
* `TauCeti.locallyFiniteSum_mem_classicalPseudodifferentialOperators`: a locally finite sum
  `ContMDiffMap.locallyFiniteSum P hP = ∑ᵢ Pᵢ` of classical pseudodifferential operators of
  order `m` is one, provided each `Pᵢ` has outputs supported in a compact set `Sᵢ` and only sees its
  input near `Sᵢ`, with `(Sᵢ)` locally finite. Near a compact set only finitely many `Pᵢ` matter.
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

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]

/-! ### Properly supported operators -/

section ProperSupport

/-- An operator `P` on the complex-valued smooth functions on `M` is **properly supported** when
for every compact set `K` there is a compact set `K'` such that `P f` is supported in `K'`
whenever `f` is supported in `K`, and `P f` vanishes on `K` whenever `f` vanishes on a
neighbourhood of `K'`. -/
def IsProperlySupported
    (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) : Prop :=
  ∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
    (∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
      tsupport f ⊆ K → tsupport (P f) ⊆ K') ∧
      ∀ f, (∀ᶠ y in 𝓝ˢ K', f y = 0) → ∀ x ∈ K, P f x = 0

variable {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

theorem isProperlySupported_iff :
    IsProperlySupported P ↔ ∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
      (∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        tsupport f ⊆ K → tsupport (P f) ⊆ K') ∧
        ∀ f, (∀ᶠ y in 𝓝ˢ K', f y = 0) → ∀ x ∈ K, P f x = 0 :=
  Iff.rfl

theorem isProperlySupported_zero :
    IsProperlySupported (0 : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :=
  fun K hK ↦ ⟨K, hK, by simp, by simp⟩

theorem isProperlySupported_id :
    IsProperlySupported (LinearMap.id : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :=
  fun K hK ↦ ⟨K, hK, fun _ hf ↦ hf, fun _ hf x hx ↦ hf.self_of_nhdsSet x hx⟩

theorem IsProperlySupported.add (hP : IsProperlySupported P) (hQ : IsProperlySupported Q) :
    IsProperlySupported (P + Q) := by
  intro K hK
  obtain ⟨K₁, hK₁, hP₁, hP₂⟩ := hP K hK
  obtain ⟨K₂, hK₂, hQ₁, hQ₂⟩ := hQ K hK
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · rw [LinearMap.add_apply, ContMDiffMap.coe_add]
    exact (tsupport_add _ _).trans (union_subset_union (hP₁ f hf) (hQ₁ f hf))
  · rw [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply,
      hP₂ f (hf.filter_mono (nhdsSet_mono subset_union_left)) x hx,
      hQ₂ f (hf.filter_mono (nhdsSet_mono subset_union_right)) x hx, add_zero]

theorem IsProperlySupported.smul (hP : IsProperlySupported P) (c : ℂ) :
    IsProperlySupported (c • P) := by
  intro K hK
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · refine (closure_mono (Function.support_subset_iff'.2 fun x hx ↦ ?_)).trans (hP₁ f hf)
    simp [ContMDiffMap.complex_smul_apply, Function.notMem_support.1 hx]
  · simp [ContMDiffMap.complex_smul_apply, hP₂ f hf x hx]

/-- Multiplying a properly supported operator on the left by a smooth function keeps it properly
supported. -/
theorem IsProperlySupported.mulLeft_comp (hP : IsProperlySupported P)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    IsProperlySupported (LinearMap.mulLeft ℂ g ∘ₗ P) := by
  intro K hK
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
    exact tsupport_mul_subset_right.trans (hP₁ f hf)
  · simp [hP₂ f hf x hx]

/-- Multiplying a properly supported operator on the right by a smooth function keeps it properly
supported. -/
theorem IsProperlySupported.comp_mulLeft (hP : IsProperlySupported P)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    IsProperlySupported (P ∘ₗ LinearMap.mulLeft ℂ g) := by
  intro K hK
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ hP₁ _ ?_, fun f hf ↦ hP₂ _ (hf.mono fun y hy ↦ ?_)⟩
  · rw [LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
    exact tsupport_mul_subset_right.trans hf
  · simp [hy]

/-- A **local** operator, one such that `P f` vanishes at every point near which `f` vanishes, is
properly supported, with `K' = K`. -/
theorem IsProperlySupported.of_local
    (hP : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → P f x = 0) : IsProperlySupported P := by
  refine fun K hK ↦ ⟨K, hK, fun f hf ↦ ?_,
    fun f hf x hx ↦ hP f x (hf.filter_mono (nhds_le_nhdsSet hx))⟩
  refine (closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport f)).trans hf
  by_contra h
  exact hx (hP f x (notMem_tsupport_iff_eventuallyEq.1 h))

/-! #### Locally finite sums -/

variable {ι : Type*}
  {P : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {hP : ∀ f, LocallyFinite fun i ↦ Function.support (P i f)} {S : ι → Set M}

/-- A locally finite sum of operators `Pᵢ` with outputs supported in compact sets `Sᵢ`, each only
seeing its input near `Sᵢ`, is properly supported. -/
theorem isProperlySupported_locallyFiniteSum [T2Space M] (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0) :
    IsProperlySupported (ContMDiffMap.locallyFiniteSum P hP) := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  -- Only the finitely many `Pᵢ` with `Sᵢ` meeting `K` see functions supported in `K` or act at
  -- points of `K`, so `K'` is the union of their sets `Sᵢ`.
  set I := (hS.finite_nonempty_inter_compact hK).toFinset
  refine ⟨⋃ i ∈ I, S i, I.isCompact_biUnion fun i _ ↦ hSc i, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · refine closure_minimal (fun x hx ↦ ?_)
      (I.finite_toSet.isClosed_biUnion fun i _ ↦ (hSc i).isClosed)
    obtain ⟨i, hi⟩ : ∃ i, P i f x ≠ 0 := by
      by_contra! h
      exact hx (by rw [ContMDiffMap.locallyFiniteSum_apply, finsum_eq_zero_of_forall_eq_zero h])
    -- `f` vanishes off `K`, so `Pᵢ f = 0` unless `Sᵢ` meets `K`.
    have hiI : i ∈ I := by
      by_contra hiI
      refine hi ?_
      rw [hloc i f ?_, ContMDiffMap.coe_zero, Pi.zero_apply]
      refine Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhdsSet.2 fun y hy hyK ↦
        hiI ((hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨y, hy, hyK⟩)) fun y hy ↦ ?_
      exact image_eq_zero_of_notMem_tsupport fun h ↦ hy (hf h)
    exact mem_biUnion hiI (hsupp i f (subset_tsupport _ hi))
  · rw [ContMDiffMap.locallyFiniteSum_apply_eq_sum hS hsupp hK f hx]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [hloc i f (hf.filter_mono (nhdsSet_mono (subset_biUnion_of_mem hi))),
      ContMDiffMap.coe_zero, Pi.zero_apply]

end ProperSupport

variable [T2Space M]

/-! ### Classical pseudodifferential operators -/

/-- The **classical pseudodifferential operators of order `m`** on a manifold `M` modelled on
`ℝⁿ`: the complex-linear operators `P` on the complex-valued smooth functions on `M` such that

* `P` is properly supported (`TauCeti.IsProperlySupported`): for every compact set `K` there is a
  compact set `K'` such that `P f` is supported in `K'` whenever `f` is supported in `K`, and
  `P f` vanishes on `K` whenever `f` vanishes on a neighbourhood of `K'`;
* for every chart `e` of the maximal smooth atlas and all cutoffs `φ`, `ψ` with compact supports
  in the chart target, the chart compression `u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` agrees on Schwartz
  functions with the quantization `Op(a)` of a classical symbol `a` of order `m`. -/
def classicalPseudodifferentialOperators (m : ℝ) :
    Submodule ℂ (C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) where
  carrier := {P | IsProperlySupported P ∧
    ∀ (e : OpenPartialHomeomorph M (CoordinateSpace n))
      (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)), ∃ a : ClassicalSymbol n ℂ ℂ m,
        ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
          quantizeSchwartzValue a.toSymbol.coefficient u x =
            e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x}
  zero_mem' := ⟨isProperlySupported_zero, fun _ _ _ _ ↦ ⟨0, fun u x ↦ by
    simp [ClassicalSymbol.toSymbol_zero, Symbol.coefficient_zero]⟩⟩
  add_mem' {P Q} hP hQ := ⟨hP.1.add hQ.1, fun e he φ ψ ↦
    let ⟨a, ha⟩ := hP.2 e he φ ψ
    let ⟨b, hb⟩ := hQ.2 e he φ ψ
    ⟨a + b, fun u x ↦ by
      rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_add, ha, hb, map_add,
        LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply]⟩⟩
  smul_mem' c P hP := ⟨hP.1.smul c, fun e he φ ψ ↦
    let ⟨a, ha⟩ := hP.2 e he φ ψ
    ⟨c • a, fun u x ↦ by
      rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_smul, ha, map_smul, LinearMap.smul_apply,
        ContMDiffMap.complex_smul_apply, smul_eq_mul]⟩⟩

theorem mem_classicalPseudodifferentialOperators_iff {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} :
    P ∈ classicalPseudodifferentialOperators m ↔ IsProperlySupported P ∧
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

/-! ### Locally finite sums of pseudodifferential operators -/

section LocallyFiniteSum

variable {m : ℝ} {ι : Type*}
  {P : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {hP : ∀ f, LocallyFinite fun i ↦ Function.support (P i f)} {S : ι → Set M}

/-- **Locally finite sums of pseudodifferential operators.** Let `Pᵢ` be classical
pseudodifferential operators of order `m` on `M`, and `Sᵢ` compact sets forming a locally finite
family, such that the outputs of `Pᵢ` are supported in `Sᵢ` and `Pᵢ f = 0` whenever `f` vanishes
near `Sᵢ`. Then the locally finite sum `f ↦ ∑ᵢ Pᵢ f` is a classical pseudodifferential operator of
order `m`. -/
theorem locallyFiniteSum_mem_classicalPseudodifferentialOperators (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hPm : ∀ i, P i ∈ classicalPseudodifferentialOperators m)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0) :
    ContMDiffMap.locallyFiniteSum P hP ∈ classicalPseudodifferentialOperators m := by
  classical
  refine mem_classicalPseudodifferentialOperators_iff.2
    ⟨isProperlySupported_locallyFiniteSum hS hSc hsupp hloc, fun e he φ ψ ↦ ?_⟩
  -- In a chart, only the finitely many `Pᵢ` with `Sᵢ` meeting `e⁻¹(supp φ)` contribute.
  have hK := e.isCompact_symm_image_tsupport φ
  set I := (hS.finite_nonempty_inter_compact hK).toFinset
  choose a ha using fun i ↦ (mem_classicalPseudodifferentialOperators_iff.1 (hPm i)).2 e he φ ψ
  refine ⟨∑ i ∈ I, a i, fun u x ↦ ?_⟩
  rw [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left]
  simp only [ha, OpenPartialHomeomorph.complexChartCompression_apply, ← Finset.smul_sum]
  by_cases hx : φ x = 0
  · simp [hx]
  rw [ContMDiffMap.locallyFiniteSum_apply_eq_sum hS hsupp hK _ ⟨x, subset_tsupport _ hx, rfl⟩]

end LocallyFiniteSum

/-! ### Multiplication operators -/

section Multiplication

/-- The cutoff `φ · L (g ∘ e⁻¹)` in a chart `e`, for a complex-valued smooth function `g` on `M`
and a real-linear functional `L` on `ℂ`. For `L` the real and the imaginary part, these cutoffs
split `φ · (g ∘ e⁻¹)`, as the next lemma shows. -/
private def chartPartCutoff {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (L : ℂ →L[ℝ] ℝ)
    (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) : 𝓓(⟨e.target, e.open_target⟩, ℝ) :=
  TestFunction.smulLeftCLMOfContDiffOn (L.contDiff.comp_contDiffOn (contMDiffOn_iff_contDiffOn.1
    (g.contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)))) φ

omit [T2Space M] in
/-- The cutoffs by the real and imaginary parts of `g` in the chart add up to `φ · (g ∘ e⁻¹)`. -/
private theorem chartPartCutoff_re_add_im {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (y : CoordinateSpace n) :
    (chartPartCutoff he g Complex.reCLM φ y : ℂ) +
        Complex.I * chartPartCutoff he g Complex.imCLM φ y = φ y * g (e.symm y) := by
  simp only [chartPartCutoff, TestFunction.smulLeftCLMOfContDiffOn_apply, Function.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im (g (e.symm y))]
  push_cast
  ring

/-- **The identity is a classical pseudodifferential operator of order `0`.** In a chart, its
compression by `φ` and `ψ` is multiplication by `φ ψ`, the quantization of the symbol `φ(x) ψ(x)`
of order `0`. -/
theorem id_mem_classicalPseudodifferentialOperators :
    LinearMap.id ∈ classicalPseudodifferentialOperators (n := n) (M := M) 0 := by
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨isProperlySupported_id, fun e he φ ψ ↦ ?_⟩
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
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1.mulLeft_comp g, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a₁, ha₁⟩ := hP.2 e he (chartPartCutoff he g Complex.reCLM φ) ψ
  obtain ⟨a₂, ha₂⟩ := hP.2 e he (chartPartCutoff he g Complex.imCLM φ) ψ
  refine ⟨a₁ + Complex.I • a₂, fun u x ↦ ?_⟩
  rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_add,
    ClassicalSymbol.quantizeSchwartzValue_toSymbol_smul, ha₁, ha₂, smul_eq_mul]
  simp only [OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, ContMDiffMap.coe_mul, Pi.mul_apply, Complex.real_smul]
  linear_combination
    P (e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) (e.symm x) *
      chartPartCutoff_re_add_im he g φ x

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
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP.1.comp_mulLeft g, fun e he φ ψ ↦ ?_⟩
  set ψ₁ := chartPartCutoff he g Complex.reCLM ψ
  set ψ₂ := chartPartCutoff he g Complex.imCLM ψ
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
    · have h := chartPartCutoff_re_add_im he g ψ (e y)
      rw [e.left_inv hy] at h
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coe_add, Pi.add_apply,
        ContMDiffMap.complex_smul_apply,
        OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ hy, Complex.real_smul]
      linear_combination -f (e y) * h
    · simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hy]
  rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_add,
    ClassicalSymbol.quantizeSchwartzValue_toSymbol_smul, ha₁, ha₂, smul_eq_mul]
  simp only [OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, key, map_add, map_smul, ContMDiffMap.coe_add, Pi.add_apply,
    ContMDiffMap.complex_smul_apply, smul_add, Complex.real_smul]
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
  -- Like `D`, its complexification is local, so it is properly supported.
  have hloc (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M)
      (hf : ∀ᶠ y in 𝓝 x, f y = 0) : ContMDiffMap.complexifyLinearMap D f x = 0 := by
    have hD₀ (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hg : ∀ᶠ y in 𝓝 x, g y = 0) :
        D g x = 0 := by
      simpa using differentialOperators_apply_eq_of_eventuallyEq hD (g := 0) hg
    simp [ContMDiffMap.complex_smul_apply, ContMDiffMap.ofReal_apply,
      hD₀ (ContMDiffMap.re f) (hf.mono fun y hy ↦ by simp [ContMDiffMap.re_apply, hy]),
      hD₀ (ContMDiffMap.im f) (hf.mono fun y hy ↦ by simp [ContMDiffMap.im_apply, hy])]
  refine mem_classicalPseudodifferentialOperators_iff.2
    ⟨IsProperlySupported.of_local hloc, fun e he φ ψ ↦ ?_⟩
  refine ⟨ClassicalSymbol.ofDifferentialOperator ℂ
    (e.chartCompressionDifferentialOperators he φ ψ m ⟨D, hD⟩), fun u x ↦ ?_⟩
  rw [ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_chartCompression]
  -- The real and imaginary parts of `u` as smooth functions, in the form in which they enter
  -- the compression of `D`; both sides evaluate to `(u y).re` (resp. `(u y).im`). The right-hand
  -- sides are anonymous constructors, which elaborate to bare subtypes that no simp lemma
  -- evaluates, so `rfl` unfolds their coercions to `fun y ↦ (u y).re` (resp. `.im`).
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
  rw [OpenPartialHomeomorph.complexChartCompression_complexifyLinearMap,
    ContMDiffMap.complexifyLinearMap_apply]
  simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.complex_smul_apply,
    ContMDiffMap.ofReal_apply, OpenPartialHomeomorph.chartCompression_apply]
  rw [hre, him]
  push_cast
  ring

end TauCeti
