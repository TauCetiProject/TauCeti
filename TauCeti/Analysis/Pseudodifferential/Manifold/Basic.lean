/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.ChartCompression
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.LocallyFiniteSum
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
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
  scalar multiples, compositions (`TauCeti.IsProperlySupported.comp`), products with smooth
  functions on either side and local operators (`TauCeti.IsProperlySupported.of_local`) are
  properly supported. A local operator takes the same value at `x` on functions that agree near
  `x` (`TauCeti.apply_eq_of_eventuallyEq_of_local`) and does not enlarge supports
  (`TauCeti.apply_eq_zero_of_notMem_tsupport_of_local`).
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
* `TauCeti.conj_mem_classicalPseudodifferentialOperators_iff`: invariance under diffeomorphisms.
  For a diffeomorphism `Φ : N → M`, the transport `f ↦ (P (f ∘ Φ⁻¹)) ∘ Φ` of `P` to `N` is a
  classical pseudodifferential operator of order `m` exactly when `P` is one; proper support is
  transported by `TauCeti.IsProperlySupported.conj`. Since the class is defined through every
  chart of the maximal atlas, the chart compressions of the transport are chart compressions of `P`
  (`OpenPartialHomeomorph.complexChartCompression_conj`).
* `TauCeti.mem_classicalPseudodifferentialOperators_of_dim_eq_zero`: on a manifold modelled on `ℝ⁰`,
  every properly supported operator has every order.
* `TauCeti.id_mem_classicalPseudodifferentialOperators` and
  `TauCeti.mulLeft_mem_classicalPseudodifferentialOperators`: the identity and multiplication by a
  smooth function have order `0`.
* `TauCeti.mulLeft_comp_mem_classicalPseudodifferentialOperators` and
  `TauCeti.comp_mulLeft_mem_classicalPseudodifferentialOperators`: multiplying an operator of order
  `m` by a smooth function, on either side, gives an operator of order `m`.
* `TauCeti.complexifyLinearMap_mem_classicalPseudodifferentialOperators`: the complexification of a
  differential operator of order at most `m` on the real-valued smooth functions on `M`, in
  Grothendieck's sense, is a classical pseudodifferential operator of order `m`. Its symbol in a
  chart is the polynomial symbol of the compression, with no smoothing remainder
  (`ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression`).

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

/-- **Composition.** The composition of two properly supported operators is properly
supported. -/
theorem IsProperlySupported.comp (hP : IsProperlySupported P) (hQ : IsProperlySupported Q) :
    IsProperlySupported (P ∘ₗ Q) := by
  have := ChartedSpace.locallyCompactSpace (CoordinateSpace n) M
  intro K hK
  obtain ⟨K₁, hK₁, hQ₁, -⟩ := hQ K hK
  obtain ⟨K₂, hK₂, hP₁, -⟩ := hP K₁ hK₁
  obtain ⟨K₃, hK₃, -, hP₂⟩ := hP K hK
  obtain ⟨L, hL, hK₃L⟩ := exists_compact_superset hK₃
  obtain ⟨K₄, hK₄, -, hQ₂⟩ := hQ L hL
  refine ⟨K₂ ∪ K₄, hK₂.union hK₄, fun f hf ↦ (hP₁ _ (hQ₁ f hf)).trans subset_union_left,
    fun f hf ↦ hP₂ (Q f) ?_⟩
  have hQf := hQ₂ f (hf.filter_mono (nhdsSet_mono subset_union_right))
  exact Filter.mem_of_superset (isOpen_interior.mem_nhdsSet.2 hK₃L) fun y hy ↦
    hQf y (interior_subset hy)

/-- A local operator, one such that `P f` vanishes at every point near which `f` vanishes, takes
the same value at `x` on two functions that agree near `x`. -/
theorem apply_eq_of_eventuallyEq_of_local
    (hP : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → P f x = 0)
    {f g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M} (hfg : (f : M → ℂ) =ᶠ[𝓝 x] g) :
    P f x = P g x := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← ContMDiffMap.coe_sub, ← map_sub]
  exact hP _ x (hfg.mono fun y hy ↦ by simp [hy])

/-- A local operator, one such that `P f` vanishes at every point near which `f` vanishes, does
not enlarge supports. -/
theorem apply_eq_zero_of_notMem_tsupport_of_local
    (hP : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → P f x = 0)
    {f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M} (hx : x ∉ tsupport f) :
    P f x = 0 :=
  hP f x (notMem_tsupport_iff_eventuallyEq.1 hx)

/-- A **local** operator, one such that `P f` vanishes at every point near which `f` vanishes, is
properly supported, with `K' = K`. -/
theorem IsProperlySupported.of_local
    (hP : ∀ f x, (∀ᶠ y in 𝓝 x, f y = 0) → P f x = 0) : IsProperlySupported P := by
  refine fun K hK ↦ ⟨K, hK, fun f hf ↦ ?_,
    fun f hf x hx ↦ hP f x (hf.filter_mono (nhds_le_nhdsSet hx))⟩
  refine (closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport f)).trans hf
  by_contra h
  exact hx (apply_eq_zero_of_notMem_tsupport_of_local hP h)

/-- **Proper support under a diffeomorphism.** Transporting a properly supported operator `P` on
`M` to `N` along a diffeomorphism `Φ : N → M`, by conjugation `f ↦ (P (f ∘ Φ⁻¹)) ∘ Φ` with the
pullback, gives a properly supported operator. -/
theorem IsProperlySupported.conj (hP : IsProperlySupported P) {N : Type*} [TopologicalSpace N]
    [ChartedSpace (CoordinateSpace n) N]
    (Φ : N ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M) :
    IsProperlySupported (Φ.compRightComplexAlgEquiv.toLinearEquiv.conj P) := by
  have hconj (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), N; 𝓘(ℝ, ℂ), ℂ⟯) :
      ⇑(Φ.compRightComplexAlgEquiv.toLinearEquiv.conj P f) =
        P (Φ.symm.compRightComplexAlgEquiv f) ∘ Φ.toHomeomorph := by
    ext x
    simp
  have hsymm (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), N; 𝓘(ℝ, ℂ), ℂ⟯) :
      ⇑(Φ.symm.compRightComplexAlgEquiv f) = f ∘ Φ.symm.toHomeomorph := by
    rw [Diffeomorph.coe_compRightComplexAlgEquiv_apply, Diffeomorph.coe_toHomeomorph]
  intro K hK
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP (Φ '' K) (hK.image Φ.continuous)
  refine ⟨Φ.symm '' K', hK'.image Φ.symm.continuous, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · have hf' : tsupport (Φ.symm.compRightComplexAlgEquiv f) ⊆ Φ '' K := by
      rw [hsymm, tsupport_comp_eq_preimage]
      exact fun z hz ↦ ⟨Φ.symm z, hf hz, Φ.apply_symm_apply z⟩
    rw [hconj, tsupport_comp_eq_preimage]
    exact fun x hx ↦ ⟨Φ x, hP₁ _ hf' hx, Φ.symm_apply_apply x⟩
  · have hf' : ∀ᶠ y in 𝓝ˢ K', Φ.symm.compRightComplexAlgEquiv f y = 0 :=
      ((Φ.symm.continuous.tendsto_nhdsSet (mapsTo_image _ _)).eventually hf).mono fun y hy ↦ by
        rwa [Diffeomorph.compRightComplexAlgEquiv_apply]
    rw [hconj, Function.comp_apply, Diffeomorph.coe_toHomeomorph]
    exact hP₂ _ hf' (Φ x) (mem_image_of_mem Φ hx)

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

/-- The symbol of a chart compression by `φ` and `ψ` has compact spatial support, since every
output of the compression is supported in the compact support of `φ`. -/
theorem hasCompactSpatialSupport_of_eq_complexChartCompression {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {b : ClassicalSymbol n ℂ ℂ m}
    (hb : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue b.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y) :
    b.toSymbol.HasCompactSpatialSupport := by
  refine Symbol.hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset.2
    ⟨tsupport φ, φ.hasCompactSupport.isCompact, fun u _ ↦ ?_⟩
  rw [show quantizeSchwartzValue b.toSymbol.coefficient u = fun y ↦ φ y •
      P (e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) (e.symm y) from
    funext fun y ↦ by rw [hb, OpenPartialHomeomorph.complexChartCompression_apply]]
  exact tsupport_smul_subset_left _ _

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

/-- **Dimension zero.** On a manifold modelled on `ℝ⁰`, every properly supported operator is a
classical pseudodifferential operator of every order: each chart compression is multiplication by
a constant, and on `ℝ⁰` a constant symbol is classical of every order. -/
theorem mem_classicalPseudodifferentialOperators_of_dim_eq_zero (hn : n = 0)
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : IsProperlySupported P) (m : ℝ) : P ∈ classicalPseudodifferentialOperators m := by
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP, fun e he φ ψ ↦ ?_⟩
  set A := e.complexChartCompression he φ ψ P
  obtain ⟨b, hb⟩ := Symbol.isSmoothing_iff.1
    (Symbol.isSmoothing_of_dim_eq_zero hn (Symbol.const (A 1 0 • ContinuousLinearMap.id ℂ ℂ))) m
  refine ⟨ClassicalSymbol.ofIsSmoothing b (Symbol.isSmoothing_of_dim_eq_zero hn b), fun u x ↦ ?_⟩
  subst hn
  -- On `ℝ⁰` the input is the constant `u x`, so the compression multiplies it by `A 1 0`.
  have hu : ContMDiffMap.ofContDiff u (u.smooth ⊤) = u x • 1 := by
    ext y
    simp [Subsingleton.elim y x]
  rw [ClassicalSymbol.toSymbol_ofIsSmoothing, hb, Symbol.quantizeSchwartzValue_const, hu,
    map_smul, ContMDiffMap.complex_smul_apply, Subsingleton.elim x 0]
  simp [mul_comm]

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

/-! ### Invariance under diffeomorphisms -/

section Diffeomorph

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (CoordinateSpace n) N] [T2Space N]

/-- **Invariance under diffeomorphisms.** Transporting a classical pseudodifferential operator `P`
of order `m` on `M` to `N` along a diffeomorphism `Φ : N → M`, by conjugation
`f ↦ (P (f ∘ Φ⁻¹)) ∘ Φ` with the pullback, gives a classical pseudodifferential operator of order
`m` on `N`. Its chart compression in a chart `e` of `N` is the chart compression of `P` in the
chart `e ∘ Φ⁻¹` of `M` (`OpenPartialHomeomorph.complexChartCompression_conj`). -/
theorem conj_mem_classicalPseudodifferentialOperators [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (Φ : N ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M) {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : P ∈ classicalPseudodifferentialOperators m) :
    Φ.compRightComplexAlgEquiv.toLinearEquiv.conj P ∈ classicalPseudodifferentialOperators m := by
  rw [mem_classicalPseudodifferentialOperators_iff] at hP ⊢
  refine ⟨hP.1.conj Φ, fun e he φ ψ ↦ ?_⟩
  obtain ⟨a, ha⟩ := hP.2 _ (Φ.symm.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he) φ ψ
  exact ⟨a, fun u x ↦ (ha u x).trans
    (DFunLike.congr_fun (LinearMap.congr_fun (e.complexChartCompression_conj he Φ φ ψ P) _) x).symm⟩

/-- **Invariance under diffeomorphisms.** For a diffeomorphism `Φ : N → M`, an operator `P` on `M`
is a classical pseudodifferential operator of order `m` if and only if its transport
`f ↦ (P (f ∘ Φ⁻¹)) ∘ Φ` to `N` is one. -/
theorem conj_mem_classicalPseudodifferentialOperators_iff
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N]
    (Φ : N ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M) {m : ℝ}
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} :
    Φ.compRightComplexAlgEquiv.toLinearEquiv.conj P ∈ classicalPseudodifferentialOperators m ↔
      P ∈ classicalPseudodifferentialOperators m := by
  refine ⟨fun h ↦ ?_, conj_mem_classicalPseudodifferentialOperators Φ⟩
  have h' := conj_mem_classicalPseudodifferentialOperators Φ.symm h
  rwa [← Diffeomorph.compRightComplexAlgEquiv_symm, AlgEquiv.toLinearEquiv_symm,
    LinearEquiv.conj_symm_conj] at h'

end Diffeomorph

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

/-- **The identity in a chart.** The compression of the identity by `φ` and `ψ` in a chart is
multiplication by `φ ψ`, the quantization of the symbol `φ(x) ψ(x)` of order `0`. -/
theorem ClassicalSymbol.quantizeSchwartzValue_ofSpatial_eq_complexChartCompression_id
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue
      (ClassicalSymbol.ofSpatial
        (fun y ↦ Complex.ofRealCLM (φ y * ψ y) • ContinuousLinearMap.id ℂ ℂ)
        ((Complex.ofRealCLM.contDiff.comp (φ.contDiff.mul ψ.contDiff)).smul
          contDiff_const)).toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ LinearMap.id (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  rw [ClassicalSymbol.toSymbol_ofSpatial, Symbol.quantizeSchwartzValue_ofSpatial,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.id_apply]
  by_cases hφ : φ x = 0
  · simp [hφ]
  · have hx : x ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
    rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hx),
      e.right_inv hx]
    simp [Complex.real_smul, mul_assoc]

/-- **The identity is a classical pseudodifferential operator of order `0`.** In a chart, its
compression by `φ` and `ψ` is multiplication by `φ ψ`, the quantization of the symbol `φ(x) ψ(x)`
of order `0`
(`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofSpatial_eq_complexChartCompression_id`). -/
theorem id_mem_classicalPseudodifferentialOperators :
    LinearMap.id ∈ classicalPseudodifferentialOperators (n := n) (M := M) 0 :=
  mem_classicalPseudodifferentialOperators_iff.2 ⟨isProperlySupported_id, fun _ he φ ψ ↦
    ⟨_, ClassicalSymbol.quantizeSchwartzValue_ofSpatial_eq_complexChartCompression_id he φ ψ⟩⟩

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

/-- **Differential operators on manifolds are quantizations in charts.** For a differential
operator `D` of order at most `m` on the real-valued smooth functions on `M`, in Grothendieck's
sense, the chart compression of its complexification by `φ` and `ψ` agrees on Schwartz functions
with the quantization of the polynomial symbol of the chart compression of `D`
(`TauCeti.ClassicalSymbol.ofDifferentialOperator`). -/
theorem ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ClassicalSymbol.ofDifferentialOperator ℂ
        (e.chartCompressionDifferentialOperators he φ ψ m D)).toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ (ContMDiffMap.complexifyLinearMap D.val)
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
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

/-- **The complexification of a differential operator is local.** If `D` is a differential
operator on the real-valued smooth functions on `M`, in Grothendieck's sense, and the
complex-valued smooth function `f` vanishes near `x`, then the complexification of `D` sends `f`
to a function vanishing at `x`. -/
theorem complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m)
    {f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {x : M} (hf : ∀ᶠ y in 𝓝 x, f y = 0) :
    ContMDiffMap.complexifyLinearMap D f x = 0 :=
  ContMDiffMap.complexifyLinearMap_apply_eq_zero (fun g hg ↦ by
    simpa using differentialOperators_apply_eq_of_eventuallyEq hD (g := 0) hg) hf

/-- **Differential operators are classical pseudodifferential operators.** The complexification of
a differential operator `D` of order at most `m` on the real-valued smooth functions on `M`, in
Grothendieck's sense of iterated commutators with multiplication operators, is a classical
pseudodifferential operator of order `m`. In a chart, its compression is exactly the quantization
of the polynomial symbol of the compression of `D`
(`ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression`),
whose principal symbol is read from the geometric principal symbol of `D`
(`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialOperator_chartCompression`). -/
theorem complexifyLinearMap_mem_classicalPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m) :
    ContMDiffMap.complexifyLinearMap D ∈
      classicalPseudodifferentialOperators (n := n) (M := M) m := by
  -- Like `D`, its complexification is local, so it is properly supported.
  exact mem_classicalPseudodifferentialOperators_iff.2
    ⟨IsProperlySupported.of_local fun _ _ ↦
      complexifyLinearMap_apply_eq_zero_of_mem_differentialOperators hD,
      fun e he φ ψ ↦ ⟨_,
      ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression he φ
        ψ ⟨D, hD⟩⟩⟩

end TauCeti
