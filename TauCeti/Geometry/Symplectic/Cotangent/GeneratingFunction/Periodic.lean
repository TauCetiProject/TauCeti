/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Pi
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.GeneratedMap
import Mathlib.Geometry.Manifold.Algebra.Monoid
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Discrete cyclic action, fixed points, and periodic orbits of generated maps

A real function `S(q, Q)` on `M × N` generates the cotangent relation
`p = d_q S(q, Q)`, `P = -d_Q S(q, Q)` parametrized by `TauCeti.CotangentBundle.generatingSource`
and `TauCeti.CotangentBundle.generatingTarget`. When this relation over `W ⊆ M × N` is the graph of
a partial map `φ : U → T*N` (`TauCeti.CotangentBundle.IsGeneratedGraphOn`), the source projection
restricts to a bijection between `W` and `U` whose inverse sends `z ∈ U` to the base-point pair
`(z.proj, (φ z).proj)` (`TauCeti.CotangentBundle.IsGeneratedGraphOn.basePairEquiv`). Every local
canonical transformation `TauCeti.CotangentBundle.generatedMap` at an interior point of invertible
mixed Hessian satisfies this hypothesis over the open branch image of its source
(`TauCeti.CotangentBundle.isGeneratedGraphOn_generatedMap`).

For a cyclic chain of functions `S i : Q × Q → ℝ`, `i : ZMod N` (`N ≥ 1`), on domains
`W i ⊆ Q × Q`, define on the configuration domain
`cyclicConfigDomain W = {c : ZMod N → Q | ∀ i, (c i, c (i + 1)) ∈ W i}` the **cyclic action**

`cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1))`.

* **Differential and critical equations.** Varying a single vertex `c i` gives
  `d(y ↦ cyclicAction S (update c i y)) = d₁(S i)(c i, c (i + 1)) + d₂(S (i - 1))(c (i - 1), c i)`
  for all `N ≥ 1`, including `N = 1` where the single summand `y ↦ S 0 (y, y)` is differentiated
  along the diagonal (`TauCeti.CotangentBundle.mvfderiv_cyclicAction_update`), and the full
  product differential is the sum of these vertex variations along the coordinate projections
  (`TauCeti.CotangentBundle.mvfderiv_cyclicAction`). For `ModelWithCorners.pi`, a configuration `c`
  is critical (`mvfderiv = 0`) if and only if at every vertex the outgoing covector
  `generatingTarget J (S (i - 1)) (c (i - 1), c i)` of edge `i - 1` equals the incoming covector
  `generatingSource J (S i) (c i, c (i + 1))` of edge `i`
  (`TauCeti.CotangentBundle.mvfderiv_cyclicAction_eq_zero_iff`).
* **Periodic-state dictionary.** When `S i` over `W i` generates the graph of `φ i`, the cyclic
  state sequences `z : ZMod N → T*Q` with `φ i (z i) = z (i + 1)` correspond bijectively, by their
  base points `z ↦ fun i ↦ (z i).proj` and `c ↦ fun i ↦ generatingSource J (S i) (c i, c (i + 1))`,
  to the critical configurations of `cyclicAction S` in `cyclicConfigDomain W`
  (`TauCeti.CotangentBundle.periodicEquiv`,
  `TauCeti.CotangentBundle.exists_equiv_periodic_of_generating`). Recording only the initial state
  `z 0` yields the bijection with phase points fixed by the `N`-fold composite
  `Φ (N - 1) ∘ ⋯ ∘ Φ 0` whose intermediate states all lie in the domains `U i`
  (`TauCeti.CotangentBundle.compositeFixedPointEquiv`). Neither finite dimension, nor
  boundarylessness, nor symplecticity of the maps is used.
* **Iterates, cyclic shifts, and fixed points.** Taking equal summands `S i = s` gives the
  correspondence between critical points of `∑ i : ZMod N, s (c i, c (i + 1))` and marked
  `N`-periodic phase points (`f^[N] z₀ = z₀` with intermediate iterates in `u`,
  `TauCeti.CotangentBundle.iterateFixedPointEquiv`). Shifting indices by `k : ZMod N` preserves the
  configuration domain, leaves the cyclic action invariant, preserves criticality, and advances the
  marked initial state along the orbit to `f^[k.val] z₀`
  (`TauCeti.CotangentBundle.iterate_iterateFixedPointEquiv_symm_coe`,
  `TauCeti.CotangentBundle.iterateFixedPointEquiv_symm_shift`). Specializing to `N = 1` recovers
  the bijection between fixed points of `φ` and critical points of the diagonal restriction
  `q ↦ s (q, q)` on `{q | (q, q) ∈ w}`, where `d(q ↦ s (q, q)) = d₁s(q, q) + d₂s(q, q)`
  (`TauCeti.CotangentBundle.fixedPointEquiv`, Cannas da Silva, Proposition 5.1).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.1, Proposition 5.1.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989, §48.
* C. Golé, *Symplectic Twist Maps: Global Variational Techniques*, World Scientific, 2001,
  Chapter 2.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

/-! ### Partial maps whose graph is a generated cotangent relation -/

section Graph

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable (I J) in
/-- The cotangent relation generated by `S : M × N → ℝ` over `W ⊆ M × N` is the **graph** of a
partial map `φ : U → T*N` defined on `U ⊆ T*M`: the pairs `(z, φ z)` for `z : U` are precisely the
pairs `(generatingSource I S x, generatingTarget J S x)` for `x ∈ W`. -/
def IsGeneratedGraphOn (S : M × N → ℝ) (W : Set (M × N)) {U : Set (CotangentBundle I M)}
    (φ : U → CotangentBundle J N) : Prop :=
  range (fun z : U ↦ ((z : CotangentBundle I M), φ z)) = generatingCorrespondence I J S '' W

variable {S : M × N → ℝ} {W : Set (M × N)} {U : Set (CotangentBundle I M)}
  {φ : U → CotangentBundle J N}

/-- Unfolding characterization of `IsGeneratedGraphOn` as equality of graphs in `T*M × T*N`. -/
theorem isGeneratedGraphOn_def :
    IsGeneratedGraphOn I J S W φ ↔
      range (fun z : U ↦ ((z : CotangentBundle I M), φ z)) =
        generatingCorrespondence I J S '' W :=
  .rfl

/-- `S` generates the graph of `φ` over `W` if and only if every `z : U` has base pair in `W` and
satisfies the source and target equations there, and every `x ∈ W` has its source covector in `U`
mapped by `φ` to its target covector. -/
theorem isGeneratedGraphOn_iff :
    IsGeneratedGraphOn I J S W φ ↔
      (∀ z : U, ((z : CotangentBundle I M).proj, (φ z).proj) ∈ W ∧
        (z : CotangentBundle I M) =
          generatingSource I S ((z : CotangentBundle I M).proj, (φ z).proj) ∧
        φ z = generatingTarget J S ((z : CotangentBundle I M).proj, (φ z).proj)) ∧
      (∀ x ∈ W, ∃ hz : generatingSource I S x ∈ U,
        φ ⟨generatingSource I S x, hz⟩ = generatingTarget J S x) := by
  rw [isGeneratedGraphOn_def, Subset.antisymm_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun z ↦ ?_, fun x hx ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨x, hxW, hxz⟩ := h₁ ⟨z, rfl⟩
    rw [generatingCorrespondence_apply] at hxz
    obtain ⟨hsrc, htgt⟩ := Prod.mk.inj hxz
    have hx : x = ((z : CotangentBundle I M).proj, (φ z).proj) :=
      Prod.ext ((proj_generatingSource x).symm.trans (congrArg TotalSpace.proj hsrc))
        ((proj_generatingTarget x).symm.trans (congrArg TotalSpace.proj htgt))
    rw [hx] at hxW hsrc htgt
    exact ⟨hxW, hsrc.symm, htgt.symm⟩
  · obtain ⟨⟨z, hz⟩, heq⟩ := h₂ ⟨x, hx, rfl⟩
    rw [generatingCorrespondence_apply] at heq
    obtain ⟨rfl, htgt⟩ := Prod.mk.inj heq
    exact ⟨hz, htgt⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨hxW, hsrc, htgt⟩ := h₁ z
    refine ⟨((z : CotangentBundle I M).proj, (φ z).proj), hxW, ?_⟩
    rw [generatingCorrespondence_apply]
    exact Prod.ext hsrc.symm htgt.symm
  · rintro _ ⟨x, hxW, rfl⟩
    obtain ⟨hz, htgt⟩ := h₂ x hxW
    refine ⟨⟨generatingSource I S x, hz⟩, ?_⟩
    rw [generatingCorrespondence_apply]
    exact Prod.ext rfl htgt

/-- Constructor for `IsGeneratedGraphOn` from the covector equations and base-point surjectivity:
if every `z : U` has base pair in `W` and satisfies `z.2 = d_q S` and `(φ z).2 = -d_Q S`, and every
`x ∈ W` is the base pair of a source point in `U`, then the relation of `S` over `W` is the graph
of `φ`. -/
theorem IsGeneratedGraphOn.of_covector
    (hφ : ∀ z : U, ((z : CotangentBundle I M).proj, (φ z).proj) ∈ W ∧
      (z : CotangentBundle I M).2 =
        mvfderiv I (fun q ↦ S (q, (φ z).proj)) (z : CotangentBundle I M).proj ∧
      (φ z).2 = -mvfderiv J (fun y ↦ S ((z : CotangentBundle I M).proj, y)) (φ z).proj)
    (hW : ∀ x ∈ W, ∃ z : U,
      (z : CotangentBundle I M) = generatingSource I S x ∧ (φ z).proj = x.2) :
    IsGeneratedGraphOn I J S W φ := by
  refine isGeneratedGraphOn_iff.2 ⟨fun z ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨hw, h₁, h₂⟩ := hφ z
    refine ⟨hw,
      CotangentBundle.ext (proj_generatingSource ((z : CotangentBundle I M).proj, (φ z).proj)).symm
        fun v ↦ ?_,
      CotangentBundle.ext (proj_generatingTarget ((z : CotangentBundle I M).proj, (φ z).proj)).symm
        fun v ↦ ?_⟩
    · rw [generatingSource_snd]
      exact DFunLike.congr_fun h₁ v
    · rw [generatingTarget_snd]
      exact DFunLike.congr_fun h₂ v
  · obtain ⟨⟨z, hz⟩, rfl, hproj⟩ := hW x hx
    have h₂ := (hφ ⟨generatingSource I S x, hz⟩).2.2
    rw [proj_generatingSource, hproj] at h₂
    refine ⟨hz, CotangentBundle.ext (hproj.trans (proj_generatingTarget x).symm) fun v ↦ ?_⟩
    rw [generatingTarget_snd]
    exact DFunLike.congr_fun h₂ v

/-- Every point `z : U` of a generated graph has base pair `(z.proj, (φ z).proj)` in `W`. -/
theorem IsGeneratedGraphOn.proj_mem (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    ((z : CotangentBundle I M).proj, (φ z).proj) ∈ W :=
  (isGeneratedGraphOn_iff.1 h).1 z |>.1

/-- Every point `z : U` of a generated graph is the source covector of its base pair. -/
theorem IsGeneratedGraphOn.eq_generatingSource (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    (z : CotangentBundle I M) =
      generatingSource I S ((z : CotangentBundle I M).proj, (φ z).proj) :=
  (isGeneratedGraphOn_iff.1 h).1 z |>.2.1

/-- At every `z : U` of a generated graph, `φ z` is the target covector of the base pair. -/
theorem IsGeneratedGraphOn.apply_eq_generatingTarget (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    φ z = generatingTarget J S ((z : CotangentBundle I M).proj, (φ z).proj) :=
  (isGeneratedGraphOn_iff.1 h).1 z |>.2.2

/-- The covector of `z : U` is `d_q S` at `(z.proj, (φ z).proj)`. -/
theorem IsGeneratedGraphOn.snd_eq (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    (z : CotangentBundle I M).2 =
      mvfderiv I (fun q ↦ S (q, (φ z).proj)) (z : CotangentBundle I M).proj := by
  conv_lhs => rw [h.eq_generatingSource z]
  exact generatingSource_snd _

/-- The covector of `φ z` for `z : U` is `-d_Q S` at `(z.proj, (φ z).proj)`. -/
theorem IsGeneratedGraphOn.apply_snd_eq (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    (φ z).2 = -mvfderiv J (fun y ↦ S ((z : CotangentBundle I M).proj, y)) (φ z).proj := by
  conv_lhs => rw [h.apply_eq_generatingTarget z]
  exact generatingTarget_snd _

/-- For every `x ∈ W`, the source covector `generatingSource I S x` belongs to `U`. -/
theorem IsGeneratedGraphOn.generatingSource_mem (h : IsGeneratedGraphOn I J S W φ) {x : M × N}
    (hx : x ∈ W) : generatingSource I S x ∈ U :=
  ((isGeneratedGraphOn_iff.1 h).2 x hx).choose

/-- On `W`, `φ` sends the source projection of `S` to its target projection. -/
theorem IsGeneratedGraphOn.apply_generatingSource (h : IsGeneratedGraphOn I J S W φ) {x : M × N}
    (hx : x ∈ W) :
    φ ⟨generatingSource I S x, h.generatingSource_mem hx⟩ = generatingTarget J S x :=
  ((isGeneratedGraphOn_iff.1 h).2 x hx).choose_spec

/-- The domain `U` of a generated graph is the image of `W` under `generatingSource I S`. -/
theorem IsGeneratedGraphOn.domain_eq (h : IsGeneratedGraphOn I J S W φ) :
    U = generatingSource I S '' W := by
  ext z
  refine ⟨fun hz ↦ ⟨(z.proj, (φ ⟨z, hz⟩).proj), h.proj_mem ⟨z, hz⟩,
    (h.eq_generatingSource ⟨z, hz⟩).symm⟩, ?_⟩
  rintro ⟨x, hx, rfl⟩
  exact h.generatingSource_mem hx

/-- Because `φ` is single-valued on `U`, `generatingSource I S` is injective on `W`. -/
theorem IsGeneratedGraphOn.injOn_generatingSource (h : IsGeneratedGraphOn I J S W φ) :
    InjOn (generatingSource I S) W := by
  intro x₁ hx₁ x₂ hx₂ heq
  have h₁ := h.apply_generatingSource hx₁
  have h₂ := h.apply_generatingSource hx₂
  have hsub : (⟨generatingSource I S x₁, h.generatingSource_mem hx₁⟩ : U) =
      ⟨generatingSource I S x₂, h.generatingSource_mem hx₂⟩ := Subtype.ext heq
  have htgt : generatingTarget J S x₁ = generatingTarget J S x₂ :=
    h₁.symm.trans ((congrArg φ hsub).trans h₂)
  exact Prod.ext
    ((proj_generatingSource x₁).symm.trans
      ((congrArg TotalSpace.proj heq).trans (proj_generatingSource x₂)))
    ((proj_generatingTarget x₁).symm.trans
      ((congrArg TotalSpace.proj htgt).trans (proj_generatingTarget x₂)))

/-- **Base-pair parametrization of a generated graph.** When `S` over `W` generates the graph of
`φ : U → T*N`, the base-point map `z ↦ (z.proj, (φ z).proj)` and `generatingSource I S` are
mutually inverse bijections between `U` and `W`. -/
def IsGeneratedGraphOn.basePairEquiv (h : IsGeneratedGraphOn I J S W φ) : U ≃ W where
  toFun z := ⟨((z : CotangentBundle I M).proj, (φ z).proj), h.proj_mem z⟩
  invFun x := ⟨generatingSource I S x.1, h.generatingSource_mem x.2⟩
  left_inv z := Subtype.ext (h.eq_generatingSource z).symm
  right_inv x := Subtype.ext <| Prod.ext (proj_generatingSource x.1) <| by
    simpa only [proj_generatingTarget] using congrArg TotalSpace.proj (h.apply_generatingSource x.2)

/-- `basePairEquiv` sends `z : U` to its pair of base points `(z.proj, (φ z).proj)`. -/
@[simp]
theorem IsGeneratedGraphOn.basePairEquiv_apply_coe (h : IsGeneratedGraphOn I J S W φ) (z : U) :
    (h.basePairEquiv z : M × N) = ((z : CotangentBundle I M).proj, (φ z).proj) :=
  (rfl)

/-- `basePairEquiv.symm` sends `x : W` to its source covector `generatingSource I S x`. -/
@[simp]
theorem IsGeneratedGraphOn.basePairEquiv_symm_apply_coe (h : IsGeneratedGraphOn I J S W φ)
    (x : W) : (h.basePairEquiv.symm x : CotangentBundle I M) = generatingSource I S x.1 :=
  (rfl)

/-- **Transpose of a generated bijection.** If `S` over `W` generates an equivalence `e : U ≃ V`
between subsets of `T*M` and `T*N`, then `cotangentGeneratingReverse S` over `Prod.swap '' W`
generates the inverse `e.symm : V → T*M`. -/
theorem IsGeneratedGraphOn.cotangentGeneratingReverse {V : Set (CotangentBundle J N)}
    {e : U ≃ V} (h : IsGeneratedGraphOn I J S W (Subtype.val ∘ e)) :
    IsGeneratedGraphOn J I (TauCeti.cotangentGeneratingReverse S) (Prod.swap '' W)
      (Subtype.val ∘ e.symm) := by
  rw [isGeneratedGraphOn_def] at h ⊢
  ext ⟨w, z⟩
  simp only [mem_range, mem_image, Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨v, rfl, rfl⟩
    have hmem : ((e.symm v : CotangentBundle I M), (v : CotangentBundle J N)) ∈
        generatingCorrespondence I J S '' W := by
      rw [← h]
      exact ⟨e.symm v, by simp⟩
    obtain ⟨x, hxW, hxz⟩ := hmem
    refine ⟨x.swap, ⟨x, hxW, rfl⟩, ?_⟩
    have hrev := generatingCorrespondence_cotangentGeneratingReverse (I := I) (J := J) (S := S)
      x.swap
    rw [Prod.swap_swap, hxz] at hrev
    exact hrev
  · rintro ⟨_, ⟨x, hxW, rfl⟩, hy⟩
    rw [generatingCorrespondence_cotangentGeneratingReverse, Prod.swap_swap] at hy
    have hmem : (z, w) ∈ generatingCorrespondence I J S '' W :=
      ⟨x, hxW, by simpa using congrArg Prod.swap hy⟩
    rw [← h] at hmem
    obtain ⟨u, hu⟩ := hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hu
    exact ⟨e u, rfl, by simp⟩

/-- Any right inverse `β` of `generatingSource I S` on `U` makes `S` over `β '' U` generate the
graph of `Φ = generatingTarget J S ∘ β` restricted to `U`. -/
theorem IsGeneratedGraphOn.of_rightInverse {Φ : CotangentBundle I M → CotangentBundle J N}
    {β : CotangentBundle I M → M × N}
    (hβ : ∀ z ∈ U, generatingSource I S (β z) = z ∧ Φ z = generatingTarget J S (β z)) :
    IsGeneratedGraphOn I J S (β '' U) (U.domRestrict Φ) := by
  refine isGeneratedGraphOn_iff.2 ⟨fun z ↦ ?_, ?_⟩
  · obtain ⟨hsrc, htgt⟩ := hβ z.1 z.2
    rw [domRestrict_apply]
    have hpair : (z.1.proj, (Φ z.1).proj) = β z.1 :=
      Prod.ext ((congrArg TotalSpace.proj hsrc).symm.trans (proj_generatingSource _))
        ((congrArg TotalSpace.proj htgt).trans (proj_generatingTarget _))
    exact ⟨hpair ▸ mem_image_of_mem β z.2, by rw [hpair, hsrc], by rw [hpair, htgt]⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hsrc, htgt⟩ := hβ z hz
    have hz' : generatingSource I S (β z) ∈ U := by rwa [hsrc]
    refine ⟨hz', ?_⟩
    simp only [domRestrict_apply, hsrc, htgt]

section GeneratedMap

variable [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

/-- The branch image of the source of `generatedMap hS hx` is an open subset of `M × N`. -/
theorem isOpen_image_generatingBranch_generatedMap_source {x : M × N}
    (hS : ContMDiff (I.prod J) 𝓘(ℝ) ∞ S) (hx : (mixedHessian I J S x).IsInvertible) :
    IsOpen (generatingBranch hS hx '' (generatedMap hS hx).source) :=
  (generatingBranch hS hx).toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (generatedMap hS hx).open_source (generatedMap_source_subset hS hx)

/-- The base pair `x` belongs to the branch image of the source of `generatedMap hS hx`. -/
theorem mem_image_generatingBranch_generatedMap_source {x : M × N}
    (hS : ContMDiff (I.prod J) 𝓘(ℝ) ∞ S) (hx : (mixedHessian I J S x).IsInvertible) :
    x ∈ generatingBranch hS hx '' (generatedMap hS hx).source :=
  ⟨generatingSource I S x, mem_generatedMap_source hS hx, generatingBranch_generatingSource hS hx⟩

/-- **Every local canonical transformation `generatedMap` has a generated graph.** Over the open
neighbourhood `generatingBranch hS hx '' (generatedMap hS hx).source` of `x`, `S` generates the
graph of `generatedMap hS hx` restricted to its source. -/
theorem isGeneratedGraphOn_generatedMap {x : M × N}
    (hS : ContMDiff (I.prod J) 𝓘(ℝ) ∞ S) (hx : (mixedHessian I J S x).IsInvertible) :
    IsGeneratedGraphOn I J S (generatingBranch hS hx '' (generatedMap hS hx).source)
      ((generatedMap hS hx).source.domRestrict (generatedMap hS hx)) :=
  IsGeneratedGraphOn.of_rightInverse fun _ hz ↦
    ⟨generatingSource_generatingBranch hS hx (generatedMap_source_subset hS hx hz),
      generatedMap_apply hS hx hz⟩

end GeneratedMap

end Graph

/-! ### Cyclic configuration domain and discrete cyclic action -/

section ConfigDomain

variable {Q : Type*}

/-- The **cyclic configuration domain** of edge domains `W : ZMod N → Set (Q × Q)`: the cyclic
sequences `c : ZMod N → Q` whose every consecutive pair `(c i, c (i + 1))` belongs to `W i`. -/
def cyclicConfigDomain {N : ℕ} (W : ZMod N → Set (Q × Q)) : Set (ZMod N → Q) :=
  {c | ∀ i, (c i, c (i + 1)) ∈ W i}

/-- Explicit set-builder form of `cyclicConfigDomain`. -/
theorem cyclicConfigDomain_def {N : ℕ} (W : ZMod N → Set (Q × Q)) :
    cyclicConfigDomain W = {c | ∀ i, (c i, c (i + 1)) ∈ W i} :=
  (rfl)

/-- A cyclic sequence belongs to `cyclicConfigDomain W` iff every consecutive pair
`(c i, c (i + 1))` belongs to `W i`. -/
@[simp]
theorem mem_cyclicConfigDomain {N : ℕ} {W : ZMod N → Set (Q × Q)} {c : ZMod N → Q} :
    c ∈ cyclicConfigDomain W ↔ ∀ i, (c i, c (i + 1)) ∈ W i :=
  .rfl

/-- `cyclicConfigDomain` is monotone with respect to pointwise inclusion of the edge domains. -/
theorem cyclicConfigDomain_mono {N : ℕ} {W W' : ZMod N → Set (Q × Q)} (h : ∀ i, W i ⊆ W' i) :
    cyclicConfigDomain W ⊆ cyclicConfigDomain W' :=
  fun _ hc i ↦ h i (hc i)

/-- Shifting indices by `k : ZMod N` preserves membership in the shifted configuration domain. -/
theorem mem_cyclicConfigDomain_shift_iff {N : ℕ} {W : ZMod N → Set (Q × Q)} (k : ZMod N)
    (c : ZMod N → Q) :
    (fun i ↦ c (i + k)) ∈ cyclicConfigDomain (fun i ↦ W (i + k)) ↔ c ∈ cyclicConfigDomain W := by
  refine ⟨fun h j ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [sub_add_cancel, add_right_comm _ 1 k] using h (j - k)
  · simpa only [add_right_comm i 1 k] using h (i + k)

/-- The **discrete cyclic action** of a chain of functions `S : ZMod N → Q × Q → ℝ`:
`cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1))`. -/
def cyclicAction {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) : ℝ :=
  ∑ i : ZMod N, S i (c i, c (i + 1))

/-- Explicit finite-sum form of `cyclicAction`. -/
theorem cyclicAction_def {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) :
    cyclicAction S c = ∑ i : ZMod N, S i (c i, c (i + 1)) :=
  (rfl)

/-- The cyclic action of the zero chain vanishes identically. -/
@[simp]
theorem cyclicAction_zero {N : ℕ} [NeZero N] (c : ZMod N → Q) :
    cyclicAction (0 : ZMod N → Q × Q → ℝ) c = 0 := by
  simp [cyclicAction_def]

/-- `cyclicAction` is additive in the chain of generators. -/
theorem cyclicAction_add {N : ℕ} [NeZero N] (S T : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) :
    cyclicAction (S + T) c = cyclicAction S c + cyclicAction T c := by
  simp [cyclicAction_def, Finset.sum_add_distrib]

/-- Negating every generator negates `cyclicAction`. -/
@[simp]
theorem cyclicAction_neg {N : ℕ} [NeZero N] (S : ZMod N → Q × Q → ℝ) (c : ZMod N → Q) :
    cyclicAction (-S) c = -cyclicAction S c := by
  simp [cyclicAction_def, Finset.sum_neg_distrib]

/-- Shifting both the chain of generators and the configuration by `k : ZMod N` leaves
`cyclicAction` invariant. -/
theorem cyclicAction_shift {N : ℕ} [NeZero N] {S : ZMod N → Q × Q → ℝ} (k : ZMod N)
    (c : ZMod N → Q) :
    cyclicAction (fun i ↦ S (i + k)) (fun i ↦ c (i + k)) = cyclicAction S c := by
  simp only [cyclicAction_def, add_right_comm _ 1 k]
  exact Equiv.sum_comp (Equiv.addRight k) fun j ↦ S j (c j, c (j + 1))

/-- For equal summands, cyclic index shifts leave `cyclicAction` invariant. -/
@[simp]
theorem cyclicAction_const_shift {N : ℕ} [NeZero N] {s : Q × Q → ℝ} (k : ZMod N)
    (c : ZMod N → Q) :
    cyclicAction (fun _ : ZMod N ↦ s) (fun i ↦ c (i + k)) =
      cyclicAction (fun _ : ZMod N ↦ s) c :=
  cyclicAction_shift (S := fun _ ↦ s) k c

end ConfigDomain

section CyclicAction

variable {F K Q : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K} [TopologicalSpace Q] [ChartedSpace K Q]

/-- For `N ≥ 1`, if every edge domain `W i` is open in `Q × Q`, then `cyclicConfigDomain W` is open
in `ZMod N → Q`. -/
theorem isOpen_cyclicConfigDomain {N : ℕ} [NeZero N] {W : ZMod N → Set (Q × Q)}
    (hW : ∀ i, IsOpen (W i)) : IsOpen (cyclicConfigDomain W) := by
  have heq : cyclicConfigDomain W =
      ⋂ i : ZMod N, (fun c : ZMod N → Q ↦ (c i, c (i + 1))) ⁻¹' W i := by
    ext c
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦
    (hW i).preimage ((continuous_apply i).prodMk (continuous_apply (i + 1)))

variable {N : ℕ} [NeZero N] {S : ZMod N → Q × Q → ℝ} {W : ZMod N → Set (Q × Q)}

/-- If each `S i` is `C^n` on `W i`, then `cyclicAction S` is `C^n` on `cyclicConfigDomain W` for
the product model `ModelWithCorners.pi`. -/
theorem contMDiffOn_cyclicAction {n : WithTop ℕ∞}
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) :
    ContMDiffOn (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ) n (cyclicAction S)
      (cyclicConfigDomain W) :=
  contMDiffOn_finsetSum fun i _ ↦ (hS i).comp (contMDiffOn_apply.prodMk contMDiffOn_apply)
    fun _ hc ↦ hc i

/-- If each `S i` is differentiable at `(c i, c (i + 1))`, then `cyclicAction S` is differentiable
at `c` for the product model `ModelWithCorners.pi`. -/
theorem mdifferentiableAt_cyclicAction {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    MDifferentiableAt (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ) (cyclicAction S) c := by
  have hsum : MDifferentiableAt (ModelWithCorners.pi fun _ : ZMod N ↦ J) 𝓘(ℝ)
      (∑ i ∈ Finset.univ, fun c' : ZMod N → Q ↦ S i (c' i, c' (i + 1))) c :=
    MDifferentiableAt.sum fun i _ ↦
      (hS i).comp c (mdifferentiableAt_apply.prodMk mdifferentiableAt_apply)
  exact hsum.congr_of_eventuallyEq <| .of_forall fun c' ↦ by simp [cyclicAction_def]

/-! ### Partial differentials and critical-point equations of the cyclic action -/

/-- **Vertex variation differential of the cyclic action.** Varying a single vertex `c i` while
holding the remaining vertices fixed differentiates `S i` in its first slot and `S (i - 1)` in its
second slot; for `N = 1` both terms come from differentiating `y ↦ S 0 (y, y)` along the
diagonal. -/
theorem mvfderiv_cyclicAction_update {c : ZMod N → Q} (i : ZMod N)
    (hS : ∀ j, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S j) (c j, c (j + 1))) :
    mvfderiv J (fun y ↦ cyclicAction S (update c i y)) (c i) =
      mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
        mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) := by
  -- Identify each summand `y ↦ S j (update c i y j, update c i y (j + 1))` on the four cases for
  -- whether `j = i` and whether `j = i - 1` (both hold simultaneously when `N = 1`).
  have hterm (j : ZMod N) :
      MDifferentiableAt J 𝓘(ℝ) (fun y ↦ S j (update c i y j, update c i y (j + 1))) (c i) ∧
        mvfderiv J (fun y ↦ S j (update c i y j, update c i y (j + 1))) (c i) =
          (if j = i then mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) else 0) +
            (if j = i - 1 then mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) else 0) := by
    rcases eq_or_ne j i with hji | hji <;> rcases eq_or_ne j (i - 1) with hj_sub | hj_sub
    · -- `N = 1` case: `j = i` and `j = i - 1`, so `j + 1 = j` and the summand is `y ↦ S j (y, y)`.
      subst hji
      have hadd : j + 1 = j := by
        calc j + 1 = (j - 1) + 1 := congrArg (· + 1) hj_sub
          _ = j := sub_add_cancel j 1
      have hfun : (fun y ↦ S j (update c j y j, update c j y (j + 1))) = fun y ↦ S j (y, y) := by
        funext y
        rw [hadd, update_self]
      have hSi : MDifferentiableAt (J.prod J) 𝓘(ℝ) (S j) (c j, c j) := by
        simpa only [hadd] using hS j
      have hdiag : MDifferentiableAt J (J.prod J) (fun y : Q ↦ (y, y)) (c j) :=
        mdifferentiableAt_id.prodMk mdifferentiableAt_id
      rw [hfun]
      refine ⟨hSi.comp_of_eq (c j) hdiag rfl, ?_⟩
      simp only [← hj_sub, hadd, ite_true]
      exact hSi.mvfderiv_diag
    · -- `j = i` and `j ≠ i - 1`, so `j + 1 ≠ j` and only the first slot varies.
      subst hji
      have hne : j + 1 ≠ j := fun h ↦ hj_sub (eq_sub_of_add_eq h)
      have hfun : (fun y ↦ S j (update c j y j, update c j y (j + 1))) =
          fun x ↦ S j (x, c (j + 1)) := by
        funext y
        rw [update_self, update_of_ne hne]
      have hslice : MDifferentiableAt J (J.prod J) (fun x : Q ↦ (x, c (j + 1))) (c j) :=
        mdifferentiableAt_id.prodMk mdifferentiableAt_const
      rw [hfun]
      refine ⟨(hS j).comp_of_eq (c j) hslice rfl, ?_⟩
      simp only [ite_true, hj_sub, ite_false, add_zero]
    · -- `j ≠ i` and `j = i - 1`, so `j + 1 = i` and only the second slot varies.
      subst hj_sub
      have hfun : (fun y ↦ S (i - 1) (update c i y (i - 1), update c i y (i - 1 + 1))) =
          fun y ↦ S (i - 1) (c (i - 1), y) := by
        funext y
        rw [sub_add_cancel, update_self, update_of_ne hji]
      have hSi : MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i - 1)) (c (i - 1), c i) := by
        simpa only [sub_add_cancel] using hS (i - 1)
      have hslice : MDifferentiableAt J (J.prod J) (fun y : Q ↦ (c (i - 1), y)) (c i) :=
        mdifferentiableAt_const.prodMk mdifferentiableAt_id
      rw [hfun]
      refine ⟨hSi.comp_of_eq (c i) hslice rfl, ?_⟩
      simp only [hji, ite_false, ite_true, zero_add]
    · -- `j ≠ i` and `j ≠ i - 1`, so neither endpoint is `i` and the summand is constant.
      have hne : j + 1 ≠ i := fun h ↦ hj_sub (eq_sub_of_add_eq h)
      have hfun : (fun y ↦ S j (update c i y j, update c i y (j + 1))) =
          fun _ ↦ S j (c j, c (j + 1)) := by
        funext y
        rw [update_of_ne hji, update_of_ne hne]
      rw [hfun]
      simp only [hji, hj_sub, ite_false, add_zero]
      exact ⟨mdifferentiableAt_const, mvfderiv_const _⟩
  simp only [cyclicAction_def]
  rw [TauCeti.mvfderiv_fun_sum fun j _ ↦ (hterm j).1]
  calc ∑ j : ZMod N, mvfderiv J (fun y ↦ S j (update c i y j, update c i y (j + 1))) (c i)
      = ∑ j : ZMod N,
          ((if j = i then mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) else 0) +
            (if j = i - 1 then mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) else 0)) :=
        Finset.sum_congr rfl fun j _ ↦ (hterm j).2
    _ = mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
          mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp

/-- **First-variation formula for the cyclic action.** On the product manifold `ZMod N → Q`, the
differential of `cyclicAction S` at `c` decomposes into the sum of vertex partial differentials
`(d₁(S i)(c i, c (i + 1)) + d₂(S (i - 1))(c (i - 1), c i)) ∘ d(eval i)`. -/
theorem mvfderiv_cyclicAction {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c =
      ∑ i : ZMod N,
        (mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) +
          mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i)).comp
            (mfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) J (fun z ↦ z i) c) := by
  rw [(mdifferentiableAt_cyclicAction hS).mvfderiv_pi_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [mvfderiv_cyclicAction_update i hS]

variable (J) in
/-- **Critical-point equations of the cyclic action (partial-differential form).** A configuration
`c : ZMod N → Q` is critical for `cyclicAction S` if and only if
`-d₂(S (i - 1))(c (i - 1), c i) = d₁(S i)(c i, c (i + 1))` at every vertex `i`. -/
theorem mvfderiv_cyclicAction_eq_zero_iff_forall_neg_mvfderiv_eq {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 ↔
      ∀ i : ZMod N,
        -mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i) =
          mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i) := by
  rw [(mdifferentiableAt_cyclicAction hS).mvfderiv_pi_eq_zero_iff]
  refine forall_congr' fun i ↦ ?_
  rw [mvfderiv_cyclicAction_update i hS, neg_eq_iff_add_eq_zero, add_comm]

variable (J) in
/-- **Critical-point equations of the cyclic action (covector matching form).** A configuration
`c : ZMod N → Q` is a critical point of `cyclicAction S` if and only if at every vertex `i` the
outgoing covector `generatingTarget J (S (i - 1)) (c (i - 1), c i)` of edge `i - 1` equals the
incoming covector `generatingSource J (S i) (c i, c (i + 1))` of edge `i`. -/
theorem mvfderiv_cyclicAction_eq_zero_iff {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 ↔
      ∀ i : ZMod N,
        generatingTarget J (S (i - 1)) (c (i - 1), c i) =
          generatingSource J (S i) (c i, c (i + 1)) := by
  rw [mvfderiv_cyclicAction_eq_zero_iff_forall_neg_mvfderiv_eq J hS]
  refine forall_congr' fun i ↦ ?_
  have hTgt : generatingTarget J (S (i - 1)) (c (i - 1), c i) =
      TotalSpace.mk' (F →L[ℝ] ℝ) (c i) (-mvfderiv J (fun y ↦ S (i - 1) (c (i - 1), y)) (c i)) :=
    CotangentBundle.ext (proj_generatingTarget _) fun _ ↦ by rw [generatingTarget_snd]; rfl
  have hSrc : generatingSource J (S i) (c i, c (i + 1)) =
      TotalSpace.mk' (F →L[ℝ] ℝ) (c i) (mvfderiv J (fun x ↦ S i (x, c (i + 1))) (c i)) :=
    CotangentBundle.ext (proj_generatingSource _) fun _ ↦ by rw [generatingSource_snd]; rfl
  rw [hTgt, hSrc, TotalSpace.mk_inj]

/-- Reversing the sign of every generator negates the differential of `cyclicAction` and preserves
its critical configurations. -/
@[simp]
theorem mvfderiv_cyclicAction_neg_eq_zero_iff (c : ZMod N → Q) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (-S)) c = 0 ↔
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 := by
  have hneg : cyclicAction (-S) = -cyclicAction S := funext (cyclicAction_neg S)
  rw [hneg, mvfderiv_neg, neg_eq_zero]

/-- Shifting both `S` and `c` by `k : ZMod N` preserves criticality of `cyclicAction`. -/
theorem mvfderiv_cyclicAction_shift_eq_zero_iff (k : ZMod N) {c : ZMod N → Q}
    (hS : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1))) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J)
        (cyclicAction (fun i ↦ S (i + k))) (fun i ↦ c (i + k)) = 0 ↔
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0 := by
  have hS' : ∀ i, MDifferentiableAt (J.prod J) 𝓘(ℝ) (S (i + k))
      (c (i + k), c (i + 1 + k)) := fun i ↦ by
    simpa only [add_right_comm i 1 k] using hS (i + k)
  rw [mvfderiv_cyclicAction_eq_zero_iff J hS', mvfderiv_cyclicAction_eq_zero_iff J hS]
  refine ⟨fun h j ↦ ?_, fun h i ↦ ?_⟩
  · have hj := h (j - k)
    simpa only [sub_add_cancel, sub_right_comm _ k 1, add_right_comm _ 1 k] using hj
  · have hi := h (i + k)
    simpa only [add_sub_right_comm, add_right_comm i 1 k] using hi

/-! ### The periodic-state / critical-configuration dictionary -/

/-- **Chain dictionary between periodic state sequences and critical configurations.** Let `S i`
over `W i` generate the graph of `φ i : U i → T*Q` for each `i : ZMod N`, and assume `S i` is
differentiable at the edges of every configuration in `cyclicConfigDomain W`. Then cyclic state
sequences `z : ZMod N → T*Q` satisfying `φ i (z i) = z (i + 1)` correspond bijectively to critical
points of `cyclicAction S` in `cyclicConfigDomain W`, via `z ↦ fun i ↦ (z i).proj` and
`c ↦ fun i ↦ generatingSource J (S i) (c i, c (i + 1))`. -/
def periodicEquiv
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i)) :
    {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} where
  toFun z := ⟨fun i ↦ (z.1 i).proj, by
    have hmem : (fun i ↦ (z.1 i).proj) ∈ cyclicConfigDomain W := fun i ↦ by
      obtain ⟨hzi, hstep⟩ := z.2 i
      simpa only [← hstep] using (hφ i).proj_mem ⟨z.1 i, hzi⟩
    refine ⟨hmem, (mvfderiv_cyclicAction_eq_zero_iff J (hSd _ hmem)).2 fun i ↦ ?_⟩
    obtain ⟨hzi, hstep⟩ := z.2 i
    obtain ⟨hzprev, hstep_prev⟩ := z.2 (i - 1)
    rw [sub_add_cancel] at hstep_prev
    have hsrc : z.1 i = generatingSource J (S i) ((z.1 i).proj, (z.1 (i + 1)).proj) := by
      simpa only [← hstep] using (hφ i).eq_generatingSource ⟨z.1 i, hzi⟩
    have htgt : z.1 i = generatingTarget J (S (i - 1)) ((z.1 (i - 1)).proj, (z.1 i).proj) := by
      rw [← hstep_prev]
      exact (hφ (i - 1)).apply_eq_generatingTarget ⟨z.1 (i - 1), hzprev⟩
    exact htgt.symm.trans hsrc⟩
  invFun c := ⟨fun i ↦ generatingSource J (S i) (c.1 i, c.1 (i + 1)), fun i ↦ by
    refine ⟨(hφ i).generatingSource_mem (c.2.1 i), ?_⟩
    rw [(hφ i).apply_generatingSource (c.2.1 i)]
    have hmatch := (mvfderiv_cyclicAction_eq_zero_iff J (hSd c.1 c.2.1)).1 c.2.2 (i + 1)
    simpa only [add_sub_cancel_right] using hmatch⟩
  left_inv z := Subtype.ext <| funext fun i ↦ by
    obtain ⟨hzi, hstep⟩ := z.2 i
    simpa only [← hstep] using ((hφ i).eq_generatingSource ⟨z.1 i, hzi⟩).symm
  right_inv c := Subtype.ext <| funext fun i ↦ proj_generatingSource (c.1 i, c.1 (i + 1))

/-- `periodicEquiv` sends a cyclic state sequence `z` to its sequence of base points
`i ↦ (z i).proj`. -/
@[simp]
theorem periodicEquiv_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (z : {z : ZMod N → CotangentBundle J Q //
      ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)}) (i : ZMod N) :
    (periodicEquiv hSd hφ z : ZMod N → Q) i = (z.1 i).proj :=
  (rfl)

/-- `periodicEquiv.symm` reconstructs the `i`-th phase state from a critical configuration `c` as
`generatingSource J (S i) (c i, c (i + 1))`. -/
@[simp]
theorem periodicEquiv_symm_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0})
    (i : ZMod N) :
    ((periodicEquiv hSd hφ).symm c : ZMod N → CotangentBundle J Q) i =
      generatingSource J (S i) (c.1 i, c.1 (i + 1)) :=
  (rfl)

/-- Smooth open-domain specialization of `periodicEquiv` when each `S i` is `C^n` (`1 ≤ n`) on an
open domain `W i ⊆ Q × Q`. -/
def periodicEquivOfContMDiffOn {n : WithTop ℕ∞} (hW : ∀ i, IsOpen (W i))
    (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) n (S i) (W i)) (hn : 1 ≤ n)
    {U : ZMod N → Set (CotangentBundle J Q)} {φ : ∀ i, U i → CotangentBundle J Q}
    (hφ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) (φ i)) :
    {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, φ i ⟨z i, h⟩ = z (i + 1)} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} :=
  periodicEquiv
    (fun _ hc i ↦ ((hS i _ (hc i)).contMDiffAt ((hW i).mem_nhds (hc i))).mdifferentiableAt
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))) hφ

/-- **Periodic states and critical points of the cyclic action** (for `N = 1`, Cannas da Silva,
Prop. 5.1, p. 29): let `S i` be smooth on open sets `W i ⊆ Q × Q`, for `i : ZMod N`, and let the
relation `p = d_q S i (q, Q)`, `P = -d_Q S i (q, Q)` over `W i` be the graph of `φ i`. The cyclic
sequences of states `z i` with `φ i (z i) = z (i + 1)` correspond, by their base points, to the
critical points of `A (q) = ∑ i, S i (q i, q (i + 1))` on the configurations whose every edge
`(q i, q (i + 1))` lies in `W i`. -/
theorem exists_equiv_periodic_of_generating [IsManifold J 1 Q]
    (hW : ∀ i, IsOpen (W i)) (hS : ∀ i, ContMDiffOn (J.prod J) 𝓘(ℝ) ∞ (S i) (W i))
    {U V : ZMod N → TopologicalSpace.Opens (CotangentBundle J Q)}
    (φ : ∀ i, U i ≃ₘ⟮J.prod 𝓘(ℝ, F →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯ V i)
    (hφ : ∀ i (z : U i),
      ((z : CotangentBundle J Q).1, (φ i z : CotangentBundle J Q).1) ∈ W i ∧
        (z : CotangentBundle J Q).2 =
          mvfderiv J (fun q ↦ S i (q, (φ i z : CotangentBundle J Q).1))
            (z : CotangentBundle J Q).1 ∧
        (φ i z : CotangentBundle J Q).2 =
          -mvfderiv J (fun y ↦ S i ((z : CotangentBundle J Q).1, y))
            (φ i z : CotangentBundle J Q).1)
    (hW' : ∀ i, ∀ x ∈ W i, ∃ z : U i,
      (z : CotangentBundle J Q) = TotalSpace.mk' (F →L[ℝ] ℝ) x.1
        (mvfderiv J (fun q ↦ S i (q, x.2)) x.1) ∧ (φ i z : CotangentBundle J Q).1 = x.2) :
    ∃ e : {z : ZMod N → CotangentBundle J Q //
          ∀ i, ∃ h : z i ∈ U i, (φ i ⟨z i, h⟩ : CotangentBundle J Q) = z (i + 1)} ≃
        {q : ZMod N → Q // (∀ i, (q i, q (i + 1)) ∈ W i) ∧
          mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J)
            (fun c : ZMod N → Q ↦ ∑ i, S i (c i, c (i + 1))) q = 0},
      ∀ z i, (e z : ZMod N → Q) i = (z.1 i).1 :=
  ⟨periodicEquivOfContMDiffOn hW hS (by simp)
      fun i ↦ IsGeneratedGraphOn.of_covector (hφ i) fun x hx ↦ by
        obtain ⟨z, hz, hproj⟩ := hW' i x hx
        refine ⟨z, hz.trans ?_, hproj⟩
        exact (CotangentBundle.ext (proj_generatingSource x) fun _ ↦ by
          rw [generatingSource_snd]; rfl).symm,
    fun _ _ ↦ rfl⟩

/-! ### Fixed points of composites, finite iterates, and cyclic shifts -/

/-- **Composite fixed-point dictionary.** For maps `Φ : ZMod N → T*Q → T*Q` whose restrictions to
`U i` are generated by `S i` over `W i`, the phase points `z₀` fixed by the `N`-fold composite
`Φ (N - 1) ∘ ⋯ ∘ Φ 0` whose intermediate states `Fin.foldl k (fun z j ↦ Φ j z) z₀` (`k < N`) all
belong to `U k` correspond bijectively to the critical configurations of `cyclicAction S` in
`cyclicConfigDomain W`, sending `z₀` to its base points along the chain and `c` to
`generatingSource J (S 0) (c 0, c 1)`. -/
def compositeFixedPointEquiv
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i))) :
    {z₀ : CotangentBundle J Q //
        (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
          Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0} :=
  let hfold (z : {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, (U i).domRestrict (Φ i) ⟨z i, h⟩ = z (i + 1)}) (k : ℕ) :
      Fin.foldl k (fun w j ↦ Φ (j : ZMod N) w) (z.1 0) = z.1 k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Fin.foldl_succ_last, Fin.val_last]
      have hcong : Fin.foldl k (fun w (j : Fin k) ↦ Φ (j.castSucc : ZMod N) w) (z.1 0) =
          Fin.foldl k (fun w (j : Fin k) ↦ Φ (j : ZMod N) w) (z.1 0) := rfl
      rw [hcong, ih, Nat.cast_add_one]
      obtain ⟨_, hstep⟩ := z.2 k
      rwa [domRestrict_apply] at hstep
  ({ toFun := fun z₀ ↦ ⟨fun i ↦ Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1, fun i ↦ by
      have hmem : Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1 ∈ U i := by
        simpa only [ZMod.natCast_zmod_val] using z₀.2.1 i.val i.val_lt
      refine ⟨hmem, ?_⟩
      dsimp only
      rw [domRestrict_apply]
      have hsucc : Φ i (Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1) =
          Fin.foldl (i.val + 1) (fun z j ↦ Φ (j : ZMod N) z) z₀.1 := by
        rw [Fin.foldl_succ_last, Fin.val_last, ZMod.natCast_zmod_val]
        rfl
      rw [hsucc]
      rcases lt_or_eq_of_le (Nat.add_one_le_iff.2 i.val_lt) with hlt | heq
      · have hval : (i + 1).val = i.val + 1 := by
          have hcast : ((i.val + 1 : ℕ) : ZMod N) = i + 1 := by
            push_cast
            rw [ZMod.natCast_zmod_val]
          rw [← hcast, ZMod.val_natCast_of_lt hlt]
        rw [hval]
      · have hi1 : i + 1 = 0 := by
          calc i + 1 = (i.val : ZMod N) + 1 := by rw [ZMod.natCast_zmod_val]
            _ = ((i.val + 1 : ℕ) : ZMod N) := by push_cast; rfl
            _ = (N : ZMod N) := by rw [heq]
            _ = 0 := ZMod.natCast_self N
        rw [heq, hi1, ZMod.val_zero, Fin.foldl_zero]
        exact z₀.2.2⟩
     invFun := fun z ↦ ⟨z.1 0, fun k _ ↦ hfold z k ▸ (z.2 k).1,
      by rw [hfold z N, ZMod.natCast_self]⟩
     left_inv := fun _ ↦ Subtype.ext (by simp)
     right_inv := fun z ↦ Subtype.ext <| funext fun i ↦
      (hfold z i.val).trans (congrArg z.1 (ZMod.natCast_zmod_val i)) } :
    {z₀ : CotangentBundle J Q //
        (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
          Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀} ≃
      {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ U i, (U i).domRestrict (Φ i) ⟨z i, h⟩ = z (i + 1)}).trans
    (periodicEquiv hSd hΦ)

/-- `compositeFixedPointEquiv` sends a fixed point `z₀` of the composite chain to the base points
of its partial composites along the chain. -/
@[simp]
theorem compositeFixedPointEquiv_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i)))
    (z₀ : {z₀ : CotangentBundle J Q //
      (∀ k < N, Fin.foldl k (fun z j ↦ Φ (j : ZMod N) z) z₀ ∈ U k) ∧
        Fin.foldl N (fun z j ↦ Φ (j : ZMod N) z) z₀ = z₀}) (i : ZMod N) :
    (compositeFixedPointEquiv hSd hΦ z₀ : ZMod N → Q) i =
      (Fin.foldl i.val (fun z j ↦ Φ (j : ZMod N) z) z₀.1).proj :=
  (rfl)

/-- `compositeFixedPointEquiv.symm` reconstructs the initial phase state `z₀` from a critical
configuration `c` as `generatingSource J (S 0) (c 0, c 1)`. -/
@[simp]
theorem compositeFixedPointEquiv_symm_apply_coe
    (hSd : ∀ c ∈ cyclicConfigDomain W, ∀ i,
      MDifferentiableAt (J.prod J) 𝓘(ℝ) (S i) (c i, c (i + 1)))
    {U : ZMod N → Set (CotangentBundle J Q)}
    {Φ : ZMod N → CotangentBundle J Q → CotangentBundle J Q}
    (hΦ : ∀ i, IsGeneratedGraphOn J J (S i) (W i) ((U i).domRestrict (Φ i)))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain W ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction S) c = 0}) :
    ((compositeFixedPointEquiv hSd hΦ).symm c : CotangentBundle J Q) =
      generatingSource J (S 0) (c.1 0, c.1 1) := by
  have h0 : ((compositeFixedPointEquiv hSd hΦ).symm c : CotangentBundle J Q) =
      ((periodicEquiv hSd hΦ).symm c : ZMod N → CotangentBundle J Q) 0 := rfl
  rw [h0, periodicEquiv_symm_apply_coe, zero_add]

section Iterates

variable {s : Q × Q → ℝ} {w : Set (Q × Q)} {u : Set (CotangentBundle J Q)}
  {f : CotangentBundle J Q → CotangentBundle J Q}

/-- **Marked `N`-periodic points and equal-summand cyclic action.** When `s` over `w` generates the
graph of `u.domRestrict f`, the marked phase points fixed by the `N`-th iterate `f^[N]` whose
intermediate iterates `f^[k] z₀` (`k < N`) all lie in `u` correspond bijectively to the critical
points of `cyclicAction (fun _ ↦ s)` in `cyclicConfigDomain (fun _ ↦ w)`. -/
def iterateFixedPointEquiv
    (hsd : ∀ x ∈ w, MDifferentiableAt (J.prod J) 𝓘(ℝ) s x)
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f)) :
    {z₀ : CotangentBundle J Q // (∀ k < N, f^[k] z₀ ∈ u) ∧ f^[N] z₀ = z₀} ≃
      {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
        mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0} :=
  let hiter (z : {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ u, u.domRestrict f ⟨z i, h⟩ = z (i + 1)}) (k : ℕ) :
      f^[k] (z.1 0) = z.1 k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Nat.cast_add_one]
      obtain ⟨_, hstep⟩ := z.2 k
      rwa [domRestrict_apply] at hstep
  ({ toFun := fun z₀ ↦ ⟨fun i ↦ f^[i.val] z₀.1, fun i ↦ by
      refine ⟨z₀.2.1 i.val i.val_lt, ?_⟩
      dsimp only
      rw [domRestrict_apply, ← Function.iterate_succ_apply' f, Nat.succ_eq_add_one]
      rcases lt_or_eq_of_le (Nat.add_one_le_iff.2 i.val_lt) with hlt | heq
      · have hval : (i + 1).val = i.val + 1 := by
          have hcast : ((i.val + 1 : ℕ) : ZMod N) = i + 1 := by
            push_cast
            rw [ZMod.natCast_zmod_val]
          rw [← hcast, ZMod.val_natCast_of_lt hlt]
        rw [hval]
      · have hi1 : i + 1 = 0 := by
          calc i + 1 = (i.val : ZMod N) + 1 := by rw [ZMod.natCast_zmod_val]
            _ = ((i.val + 1 : ℕ) : ZMod N) := by push_cast; rfl
            _ = (N : ZMod N) := by rw [heq]
            _ = 0 := ZMod.natCast_self N
        rw [heq, hi1, ZMod.val_zero, Function.iterate_zero_apply, z₀.2.2]⟩
     invFun := fun z ↦ ⟨z.1 0, fun k _ ↦ hiter z k ▸ (z.2 k).1,
      by rw [hiter z N, ZMod.natCast_self]⟩
     left_inv := fun _ ↦ Subtype.ext (by simp)
     right_inv := fun z ↦ Subtype.ext <| funext fun i ↦
      (hiter z i.val).trans (congrArg z.1 (ZMod.natCast_zmod_val i)) } :
    {z₀ : CotangentBundle J Q // (∀ k < N, f^[k] z₀ ∈ u) ∧ f^[N] z₀ = z₀} ≃
      {z : ZMod N → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ u, u.domRestrict f ⟨z i, h⟩ = z (i + 1)}).trans
    (periodicEquiv (S := fun _ ↦ s) (W := fun _ ↦ w)
      (fun _ hc i ↦ hsd _ (hc i)) (fun _ ↦ hf))

/-- `iterateFixedPointEquiv` sends a marked `N`-periodic phase point `z₀` to the base points
`i ↦ (f^[i.val] z₀).proj` of its forward orbit. -/
@[simp]
theorem iterateFixedPointEquiv_apply_coe
    (hsd : ∀ x ∈ w, MDifferentiableAt (J.prod J) 𝓘(ℝ) s x)
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (z₀ : {z₀ : CotangentBundle J Q // (∀ k < N, f^[k] z₀ ∈ u) ∧ f^[N] z₀ = z₀})
    (i : ZMod N) :
    (iterateFixedPointEquiv (N := N) hsd hf z₀ : ZMod N → Q) i = (f^[i.val] z₀.1).proj :=
  (rfl)

/-- `iterateFixedPointEquiv.symm` reconstructs the marked initial state `z₀` from a critical
configuration `c` as `generatingSource J s (c 0, c 1)`. -/
@[simp]
theorem iterateFixedPointEquiv_symm_apply_coe
    (hsd : ∀ x ∈ w, MDifferentiableAt (J.prod J) 𝓘(ℝ) s x)
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0}) :
    ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) =
      generatingSource J s (c.1 0, c.1 1) := by
  have h0 : ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) =
      ((periodicEquiv (N := N) (S := fun _ ↦ s) (W := fun _ ↦ w)
        (fun _ hc i ↦ hsd _ (hc i)) (fun _ ↦ hf)).symm c :
        ZMod N → CotangentBundle J Q) 0 := rfl
  rw [h0, periodicEquiv_symm_apply_coe, zero_add]

/-- Iterating `f` `m` times from the initial periodic state reconstructed from a critical
configuration `c` yields the source covector `generatingSource J s (c m, c (m + 1))` at residue
`(m : ZMod N)`. -/
theorem iterate_iterateFixedPointEquiv_symm_coe
    (hsd : ∀ x ∈ w, MDifferentiableAt (J.prod J) 𝓘(ℝ) s x)
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f))
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0})
    (m : ℕ) :
    f^[m] ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) =
      generatingSource J s (c.1 m, c.1 (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have hmem : (c.1 m, c.1 (m + 1)) ∈ w := c.2.1 m
    have hdom := hf.apply_generatingSource hmem
    rw [domRestrict_apply] at hdom
    have hcrit := (mvfderiv_cyclicAction_eq_zero_iff J
      (S := fun _ ↦ s) (fun i ↦ hsd _ (c.2.1 i))).1 c.2.2 (m + 1)
    rw [hdom, Nat.cast_add_one]
    simpa only [add_sub_cancel_right] using hcrit

/-- **A cyclic shift of a critical configuration is the same periodic orbit with a shifted marked
point.** Shifting `c` by `k : ZMod N` advances the corresponding initial periodic state
`z₀ = (iterateFixedPointEquiv hsd hf).symm c` to `f^[k.val] z₀`. -/
theorem iterateFixedPointEquiv_symm_shift
    (hsd : ∀ x ∈ w, MDifferentiableAt (J.prod J) 𝓘(ℝ) s x)
    (hf : IsGeneratedGraphOn J J s w (u.domRestrict f)) (k : ZMod N)
    (c : {c : ZMod N → Q // c ∈ cyclicConfigDomain (fun _ ↦ w) ∧
      mvfderiv (ModelWithCorners.pi fun _ : ZMod N ↦ J) (cyclicAction (fun _ ↦ s)) c = 0}) :
    ((iterateFixedPointEquiv (N := N) hsd hf).symm
      ⟨fun i ↦ c.1 (i + k), (mem_cyclicConfigDomain_shift_iff (W := fun _ ↦ w) k c.1).2 c.2.1,
        (mvfderiv_cyclicAction_shift_eq_zero_iff (S := fun _ ↦ s) k
          fun i ↦ hsd _ (mem_cyclicConfigDomain.1 c.2.1 i)).2 c.2.2⟩ : CotangentBundle J Q) =
      f^[k.val] ((iterateFixedPointEquiv (N := N) hsd hf).symm c : CotangentBundle J Q) := by
  rw [iterateFixedPointEquiv_symm_apply_coe, iterate_iterateFixedPointEquiv_symm_coe,
    ZMod.natCast_zmod_val]
  simp only [zero_add, add_comm 1 k]

end Iterates

/-! ### Fixed points and diagonal restriction (`N = 1`, Cannas da Silva Prop. 5.1) -/

section FixedPoints

variable {s : Q × Q → ℝ} {w : Set (Q × Q)} {u : Set (CotangentBundle J Q)}
  {φ : u → CotangentBundle J Q}

/-- On the diagonal `(q, q)`, the outgoing and incoming covectors of `s` agree if and only if `q`
is a critical point of `x ↦ s (x, x)`. -/
theorem generatingTarget_eq_generatingSource_diag_iff {q : Q}
    (hs : MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q)) :
    generatingTarget J s (q, q) = generatingSource J s (q, q) ↔
      mvfderiv J (fun x ↦ s (x, x)) q = 0 := by
  have hTgt : generatingTarget J s (q, q) =
      TotalSpace.mk' (F →L[ℝ] ℝ) q (-mvfderiv J (fun y ↦ s (q, y)) q) :=
    CotangentBundle.ext (proj_generatingTarget _) fun _ ↦ by rw [generatingTarget_snd]; rfl
  have hSrc : generatingSource J s (q, q) =
      TotalSpace.mk' (F →L[ℝ] ℝ) q (mvfderiv J (fun x ↦ s (x, q)) q) :=
    CotangentBundle.ext (proj_generatingSource _) fun _ ↦ by rw [generatingSource_snd]; rfl
  rw [hTgt, hSrc, TotalSpace.mk_inj, neg_eq_iff_add_eq_zero, add_comm, ← hs.mvfderiv_diag]

/-- For `N = 1`, a constant configuration `fun _ : ZMod 1 ↦ q` is critical for `cyclicAction` if
and only if `q` is a critical point of the diagonal function `x ↦ s (x, x)`. -/
theorem mvfderiv_cyclicAction_zmod_one_eq_zero_iff {q : Q}
    (hs : MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q)) :
    mvfderiv (ModelWithCorners.pi fun _ : ZMod 1 ↦ J)
        (cyclicAction (fun _ : ZMod 1 ↦ s)) (fun _ ↦ q) = 0 ↔
      mvfderiv J (fun x ↦ s (x, x)) q = 0 := by
  rw [mvfderiv_cyclicAction_eq_zero_iff J fun _ ↦ hs, Unique.forall_iff,
    generatingTarget_eq_generatingSource_diag_iff hs]

/-- **Fixed points and critical points of the diagonal restriction** (Cannas da Silva, Prop. 5.1,
p. 29), derived as the case `N = 1` of `periodicEquiv`: when `s` over `w ⊆ Q × Q` generates the
graph of `φ : u → T*Q` and is differentiable along the diagonal of `w`, the fixed points of `φ`
correspond bijectively to the critical points of `q ↦ s (q, q)` on `{q | (q, q) ∈ w}`, sending `z`
to `z.proj` and `q` to `generatingSource J s (q, q)`. -/
def fixedPointEquiv
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ) :
    {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z} ≃
      {q : Q // (q, q) ∈ w ∧ mvfderiv J (fun x ↦ s (x, x)) q = 0} :=
  ({ toFun := fun z ↦ ⟨fun _ : ZMod 1 ↦ z.1, fun _ ↦ z.2⟩
     invFun := fun z ↦ ⟨z.1 0, by
       simpa only [Subsingleton.elim (0 + 1 : ZMod 1) 0] using z.2 0⟩
     left_inv := fun _ ↦ Subtype.ext rfl
     right_inv := fun z ↦ Subtype.ext <| funext fun i ↦ by rw [Subsingleton.elim i 0] } :
    {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z} ≃
      {z : ZMod 1 → CotangentBundle J Q //
        ∀ i, ∃ h : z i ∈ u, φ ⟨z i, h⟩ = z (i + 1)}).trans <|
  (periodicEquiv (N := 1) (S := fun _ ↦ s) (W := fun _ ↦ w)
    (fun c hc i ↦ by
      have hi : c (i + 1) = c i := congrArg c (Subsingleton.elim _ _)
      exact hi ▸ hsd (c i) (hi ▸ hc i))
    (fun _ ↦ hφ)).trans
  { toFun := fun c ↦ ⟨c.1 0, by
      have h0 : c.1 = fun _ : ZMod 1 ↦ c.1 0 := funext fun i ↦ congrArg c.1 (Subsingleton.elim i 0)
      have hw0 : (c.1 0, c.1 0) ∈ w := by
        simpa only [Subsingleton.elim (0 + 1 : ZMod 1) 0] using c.2.1 0
      refine ⟨hw0, (mvfderiv_cyclicAction_zmod_one_eq_zero_iff (hsd _ hw0)).1 ?_⟩
      exact h0 ▸ c.2.2⟩
    invFun := fun q ↦ ⟨fun _ : ZMod 1 ↦ q.1, ⟨fun _ ↦ q.2.1,
      (mvfderiv_cyclicAction_zmod_one_eq_zero_iff (hsd _ q.2.1)).2 q.2.2⟩⟩
    left_inv := fun c ↦ Subtype.ext <| funext fun i ↦ congrArg c.1 (Subsingleton.elim 0 i)
    right_inv := fun _ ↦ Subtype.ext rfl }

/-- `fixedPointEquiv` sends a fixed point `z` of `φ` to its base point `z.proj`. -/
@[simp]
theorem fixedPointEquiv_apply_coe
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ)
    (z : {z : CotangentBundle J Q // ∃ h : z ∈ u, φ ⟨z, h⟩ = z}) :
    (fixedPointEquiv hsd hφ z : Q) = z.1.proj :=
  (rfl)

/-- `fixedPointEquiv.symm` reconstructs a fixed point from a diagonal critical point `q` as
`generatingSource J s (q, q)`. -/
@[simp]
theorem fixedPointEquiv_symm_apply_coe
    (hsd : ∀ q, (q, q) ∈ w → MDifferentiableAt (J.prod J) 𝓘(ℝ) s (q, q))
    (hφ : IsGeneratedGraphOn J J s w φ)
    (q : {q : Q // (q, q) ∈ w ∧ mvfderiv J (fun x ↦ s (x, x)) q = 0}) :
    ((fixedPointEquiv hsd hφ).symm q : CotangentBundle J Q) =
      generatingSource J s (q.1, q.1) :=
  (rfl)

end FixedPoints

end CyclicAction

end TauCeti.CotangentBundle
