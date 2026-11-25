/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Topology.LocallyConstant.Compact
public import TauCeti.Topology.LocallyConstant.Fiber

/-!
# Locally constant functions with compact support

For a topological space `X` and an additive monoid `M` (an `R`-module), this file defines the
`R`-module `C_c^∞(X, M)` of locally constant functions `X → M` with compact support,
`LocallyConstant.compactlySupported R X M`, as a submodule of `LocallyConstant X M`. No topology on
`M` is used. When `X` is an *l-space* (Hausdorff, locally compact and totally disconnected), and
in particular when `X` is a locally profinite group, these are the test functions of the smooth
representation theory of `X`: the Hecke algebra of a locally profinite group is `C_c^∞(G, A)`
under convolution, and integration against an `A`-valued Haar measure is a finite sum over a
compact-open expansion of a test function.

The expansions come from the fibres. The support of a locally constant function is clopen, so it
equals the topological support, and a compactly supported locally constant function takes finitely
many values. Its nonzero fibres are therefore finitely many pairwise disjoint compact open sets, and
`f = ∑ m • 1_{f⁻¹(m)}` (`LocallyConstant.exists_pairwiseDisjoint_sum_indicator`). In a Hausdorff
space compact open sets are clopen, so their indicators `1_K • m` are locally constant, and they
span `C_c^∞(X, M)` (`LocallyConstant.compactlySupported_eq_span`). Two such expansions have a common
refinement by `Finpartition.exists_forall_le_or_disjoint`, applied in the generalized Boolean
algebra `CompactOpens X` of compact open sets of a Hausdorff space `X`.

The test functions on a topological group, and their invariance under compact open subgroups,
are treated in `TauCeti.Topology.Algebra.Group.LocallyConstant.CompactSupport`.

## Main definitions

* `LocallyConstant.compactlySupported R X M`: the `R`-module `C_c^∞(X, M)`.
* `LocallyConstant.compactOpenIndicator K m`: in a Hausdorff space, the indicator `1_K • m` of a
  compact open set `K`, a locally constant function with compact support.

## Main results

* `LocallyConstant.exists_pairwiseDisjoint_sum_indicator`: a test function is a finite sum of
  indicators of pairwise disjoint compact open sets.
* `LocallyConstant.compactlySupported_eq_span`: in a Hausdorff space, `C_c^∞(X, M)` is spanned by
  the indicators `1_K • m` of compact open sets.
* `LocallyConstant.compactlySupported_eq_top`, `LocallyConstant.compactlySupported_eq_bot`: every
  locally constant function on a compact space is a test function, and on a preconnected
  noncompact space, such as `ℝ`, the only test function is `0`.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Lemma 1, and §1.2, pp. 7–8.
* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.1, p. 25.
-/

public section

open Function Set TopologicalSpace

namespace LocallyConstant

variable {R X M : Type*}

section Space

variable [TopologicalSpace X]

section Zero

variable [Zero M]

/-- The support of a locally constant function is clopen. -/
theorem isClopen_support (f : LocallyConstant X M) : IsClopen (support f) :=
  (f.isLocallyConstant.isClopen_fiber 0).compl

/-- The topological support of a locally constant function is its support. -/
@[simp]
theorem tsupport_eq_support (f : LocallyConstant X M) : tsupport f = support f :=
  f.isClopen_support.isClosed.closure_eq

/-- A locally constant function has compact support exactly when its support is compact. -/
theorem hasCompactSupport_iff_isCompact_support {f : LocallyConstant X M} :
    HasCompactSupport f ↔ IsCompact (support f) := by
  rw [HasCompactSupport, tsupport_eq_support]

/-- A locally constant function with compact support takes only finitely many values. -/
theorem finite_range_of_hasCompactSupport {f : LocallyConstant X M} (hf : HasCompactSupport f) :
    (range f).Finite := by
  -- Off the compact support `f` vanishes, and on it `f` takes finitely many values.
  refine ((f.isLocallyConstant.finite_image_of_isCompact hf.isCompact).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨x, hx, rfl⟩
  · exact .inl (image_eq_zero_of_notMem_tsupport hx)

/-- A compactly supported locally constant function on `X` whose support lies in a set `U`
restricts to a compactly supported function on `U`. -/
theorem hasCompactSupport_comap_subtypeVal_of_support_subset {U : Set X}
    {f : LocallyConstant X M} (hf : HasCompactSupport f) (hsupp : support f ⊆ U) :
    HasCompactSupport (f.comap ⟨Subtype.val, continuous_subtypeVal⟩ : LocallyConstant U M) := by
  rw [hasCompactSupport_iff_isCompact_support, coe_comap, ContinuousMap.coe_mk,
    support_comp_eq_preimage]
  refine Topology.IsInducing.subtypeVal.isCompact_preimage' ?_ (by rwa [Subtype.range_coe])
  rw [← tsupport_eq_support]
  exact hf.isCompact

section Indicator

variable [T2Space X]

/-- The indicator `1_K • m` of a compact open set `K` of a Hausdorff space, which is clopen: the
locally constant function taking the value `m` on `K` and `0` off `K`. -/
noncomputable def compactOpenIndicator (K : CompactOpens X) (m : M) : LocallyConstant X M :=
  (const X m).indicator K.toClopens.isClopen

/-- The underlying function of `compactOpenIndicator K m` is the set indicator of `K` with value
`m`. -/
@[simp]
theorem coe_compactOpenIndicator (K : CompactOpens X) (m : M) :
    ⇑(compactOpenIndicator K m) = (K : Set X).indicator fun _ => m :=
  funext fun x => indicator_apply _ _ x

@[simp]
theorem compactOpenIndicator_of_mem {K : CompactOpens X} {x : X} (hx : x ∈ K) (m : M) :
    compactOpenIndicator K m x = m :=
  indicator_of_mem _ _ hx

@[simp]
theorem compactOpenIndicator_of_notMem {K : CompactOpens X} {x : X} (hx : x ∉ K) (m : M) :
    compactOpenIndicator K m x = 0 :=
  indicator_of_notMem _ _ hx

@[simp]
theorem compactOpenIndicator_zero (K : CompactOpens X) :
    compactOpenIndicator K (0 : M) = 0 :=
  ext fun x => by by_cases hx : x ∈ K <;> simp [hx]

@[simp]
theorem compactOpenIndicator_bot (m : M) : compactOpenIndicator (⊥ : CompactOpens X) m = 0 :=
  ext fun x => compactOpenIndicator_of_notMem (by simp [← SetLike.mem_coe]) m

end Indicator

end Zero

section Indicator

variable [T2Space X]

/-- The indicator `1_K • m` is additive in the coefficient `m`. -/
theorem compactOpenIndicator_add [AddZeroClass M] (K : CompactOpens X) (m n : M) :
    compactOpenIndicator K (m + n) = compactOpenIndicator K m + compactOpenIndicator K n :=
  ext fun x => by by_cases hx : x ∈ K <;> simp [hx]

/-- The indicator `1_K • m` commutes with scalar multiplication of the coefficient `m`. -/
theorem compactOpenIndicator_smul [Zero M] [SMulZeroClass R M] (K : CompactOpens X) (c : R)
    (m : M) : compactOpenIndicator K (c • m) = c • compactOpenIndicator K m :=
  ext fun x => by by_cases hx : x ∈ K <;> simp [hx]

/-- The indicator of the union of two disjoint compact open sets is the sum of their
indicators. -/
theorem compactOpenIndicator_sup_of_disjoint [AddZeroClass M] {K L : CompactOpens X}
    (hKL : Disjoint K L) (m : M) :
    compactOpenIndicator (K ⊔ L) m = compactOpenIndicator K m + compactOpenIndicator L m := by
  have h : Disjoint (K : Set X) L :=
    Set.disjoint_iff_inter_eq_empty.2 (by rw [← CompactOpens.coe_inf, hKL.eq_bot,
      CompactOpens.coe_bot])
  refine ext fun x => ?_
  by_cases hK : x ∈ (K : Set X)
  · simp [Set.indicator_of_mem, hK, Set.disjoint_left.1 h hK]
  · by_cases hL : x ∈ (L : Set X) <;> simp [hK, hL]

end Indicator

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (R X M) in
/-- The `R`-module `C_c^∞(X, M)` of locally constant functions `X → M` with compact support, as a
submodule of `LocallyConstant X M`. No topology on `M` is involved. -/
def compactlySupported : Submodule R (LocallyConstant X M) where
  carrier := {f | HasCompactSupport f}
  add_mem' hf hg := hf.add hg
  zero_mem' := HasCompactSupport.zero
  smul_mem' c f hf := hf.mono (support_const_smul_subset c f)

@[simp]
theorem mem_compactlySupported {f : LocallyConstant X M} :
    f ∈ compactlySupported R X M ↔ HasCompactSupport f :=
  Iff.rfl

/-- Elements of `C_c^∞(X, M)` are determined by their values. -/
theorem compactlySupported.coeFn_injective :
    Injective fun f : compactlySupported R X M => ((f : LocallyConstant X M) : X → M) :=
  coe_injective.comp Subtype.val_injective

/-- Two elements of `C_c^∞(X, M)` are equal when they agree at every point. -/
@[ext]
theorem compactlySupported.ext {f g : compactlySupported R X M}
    (h : ∀ x, (f : LocallyConstant X M) x = (g : LocallyConstant X M) x) : f = g :=
  compactlySupported.coeFn_injective (funext h)

/-- The indicator of a compact clopen set `K`, for instance `1_K • m` when `f = const X m`, has
compact support. -/
theorem indicator_mem_compactlySupported (f : LocallyConstant X M) {K : Set X} (hK : IsClopen K)
    (hKc : IsCompact K) : f.indicator hK ∈ compactlySupported R X M :=
  HasCompactSupport.intro' hKc hK.isClosed fun _ hx => indicator_of_notMem f hK hx

/-- The indicator `1_K • m` of a compact open set has compact support. -/
theorem compactOpenIndicator_mem_compactlySupported [T2Space X] (K : CompactOpens X) (m : M) :
    compactOpenIndicator K m ∈ compactlySupported R X M :=
  indicator_mem_compactlySupported _ _ K.isCompact

/-- **Disjoint compact-open expansion.** A locally constant function `f` with compact support is
the finite sum `∑ m ∈ s, 1_{K m} • m` over finitely many nonzero values `m`, where the sets
`K m = f⁻¹(m)` are pairwise disjoint compact open sets. -/
theorem exists_pairwiseDisjoint_sum_indicator {f : LocallyConstant X M}
    (hf : HasCompactSupport f) :
    ∃ (s : Finset M) (K : M → CompactOpens X), 0 ∉ s ∧ (∀ m ∈ s, (K m : Set X) = f ⁻¹' {m}) ∧
      (s : Set M).PairwiseDisjoint (fun m => (K m : Set X)) ∧
      ⇑f = ∑ m ∈ s, (K m : Set X).indicator fun _ => m := by
  classical
  -- The fibres over nonzero values are compact open, as `f` vanishes off its compact support.
  have hf0 : ∀ x ∉ tsupport f, f x = 0 := fun _ hx => image_eq_zero_of_notMem_tsupport hx
  let K := f.isLocallyConstant.fiberCompactOpens hf.isCompact hf0
  have hK (m : M) (x : X) : x ∈ (K m : Set X) ↔ f x = m ∧ m ≠ 0 :=
    f.isLocallyConstant.mem_fiberCompactOpens hf.isCompact hf0
  refine ⟨(finite_range_of_hasCompactSupport hf).toFinset.erase 0, K, Finset.notMem_erase 0 _,
    fun m hm => ?_, f.isLocallyConstant.pairwiseDisjoint_fiberCompactOpens hf.isCompact hf0 _,
    funext fun x => ?_⟩
  · -- For `m` in the erased range, the condition `m ≠ 0` holds.
    ext x
    simp only [hK, mem_preimage, mem_singleton_iff, and_iff_left_iff_imp]
    exact fun _ => Finset.ne_of_mem_erase hm
  rw [Finset.sum_apply]
  by_cases hx : f x = 0
  · exact hx.trans (Finset.sum_eq_zero fun m _ =>
      Set.indicator_of_notMem (by simp [hK, hx, eq_comm]) _).symm
  rw [Finset.sum_eq_single_of_mem (f x) (by simp [hx]) fun m _ hm =>
    Set.indicator_of_notMem (by simp [hK, Ne.symm hm]) _]
  exact (Set.indicator_of_mem ((hK _ x).2 ⟨rfl, hx⟩) _).symm

/-- In a Hausdorff space, `C_c^∞(X, M)` is spanned by the indicators `1_K • m` of compact open
sets `K`, which are clopen. -/
theorem compactlySupported_eq_span [T2Space X] :
    compactlySupported R X M = Submodule.span R
      (range fun p : CompactOpens X × M => compactOpenIndicator p.1 p.2) := by
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨s, K, -, -, -, hfs⟩ := exists_pairwiseDisjoint_sum_indicator hf
    have hf' : f = ∑ m ∈ s, compactOpenIndicator (K m) m := by
      refine coe_injective ?_
      simp_rw [hfs, ← coe_compactOpenIndicator]
      -- `coeFnAddMonoidHom` is the coercion to functions, as an additive monoid hom.
      exact (map_sum (coeFnAddMonoidHom (X := X) (Y := M))
        (fun m => compactOpenIndicator (K m) m) s).symm
    rw [hf']
    exact Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨(K m, m), rfl⟩
  · rintro _ ⟨⟨K, m⟩, rfl⟩
    exact compactOpenIndicator_mem_compactlySupported K m

variable (R X M) in
/-- On a compact space every locally constant function has compact support. -/
theorem compactlySupported_eq_top [CompactSpace X] : compactlySupported R X M = ⊤ :=
  eq_top_iff.2 fun f _ => HasCompactSupport.of_compactSpace f

variable (R X M) in
/-- On a preconnected noncompact space, such as `ℝ`, the only locally constant function with
compact support is `0`: it is constant, and a nonzero constant has noncompact support. -/
theorem compactlySupported_eq_bot [PreconnectedSpace X] [NoncompactSpace X] :
    compactlySupported R X M = ⊥ := by
  refine eq_bot_iff.2 fun f hf => (Submodule.mem_bot R).2 (ext fun x => ?_)
  by_contra hx
  have hsupp : support f = univ := eq_univ_of_forall fun y => by
    rwa [mem_support, f.apply_eq_of_preconnectedSpace y x]
  exact noncompact_univ X (hsupp ▸ hasCompactSupport_iff_isCompact_support.1 hf)

end Module

end Space

end LocallyConstant
