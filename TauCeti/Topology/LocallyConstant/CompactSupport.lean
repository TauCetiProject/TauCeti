/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sets.Compacts
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact

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
refinement by `Finpartition.exists_forall_le_or_disjoint`, applied in the Boolean algebra of
compact open sets of `X`.

On a topological group `G`, a test function is uniformly locally constant: it is invariant under
left and right translation by an open subgroup, which can be taken compact when `G` is locally
profinite (`LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq`). For a compact open
subgroup `U`, the test functions invariant under right translation by `U` are the finitely
supported functions on `G ⧸ U` (`LocallyConstant.compactlySupportedRightInvariantEquiv`).

## Main definitions

* `LocallyConstant.compactlySupported R X M`: the `R`-module `C_c^∞(X, M)`.
* `LocallyConstant.compactlySupportedRightInvariant R M U`: the right `U`-invariant elements of
  `C_c^∞(G, M)`.
* `LocallyConstant.compactlySupportedRightInvariantEquiv`: for `U` compact open, the
  identification of the right `U`-invariant test functions with `G ⧸ U →₀ M`.

## Main results

* `LocallyConstant.exists_pairwiseDisjoint_sum_indicator`: a test function is a finite sum of
  indicators of pairwise disjoint compact open sets.
* `LocallyConstant.compactlySupported_eq_span`: in a Hausdorff space, `C_c^∞(X, M)` is spanned by
  the indicators `1_K • m` of compact open sets.
* `LocallyConstant.compactlySupported_eq_top`, `LocallyConstant.compactlySupported_eq_bot`: every
  locally constant function on a compact space is a test function, and on a preconnected
  noncompact space, such as `ℝ`, the only test function is `0`.
* `LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq`: on a locally profinite group, every
  test function is left and right invariant under some compact open subgroup.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Lemma 1, and §1.2, pp. 7–8.
* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.1, p. 25.
-/

public section

open Function Set TopologicalSpace
open scoped Pointwise

namespace LocallyConstant

variable {R X G M : Type*}

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
  have := isCompact_iff_compactSpace.1 hf.isCompact
  -- Off the compact support `f` vanishes; on it, `f` is locally constant on a compact space.
  refine ((f.isLocallyConstant.comp_continuous
    (continuous_subtype_val (p := (· ∈ tsupport f)))).range_finite.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · exact .inl (image_eq_zero_of_notMem_tsupport hx)

end Zero

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

/-- The indicator of a compact clopen set `K`, for instance `1_K • m` when `f = const X m`, has
compact support. -/
theorem indicator_mem_compactlySupported (f : LocallyConstant X M) {K : Set X} (hK : IsClopen K)
    (hKc : IsCompact K) : f.indicator hK ∈ compactlySupported R X M :=
  HasCompactSupport.intro' hKc hK.isClosed fun _ hx => indicator_of_notMem f hK hx

/-- **Disjoint compact-open expansion.** A locally constant function `f` with compact support is
the finite sum `∑ m ∈ s, 1_{K m} • m` over finitely many nonzero values `m`, where the sets
`K m = f⁻¹(m)` are pairwise disjoint compact open sets. -/
theorem exists_pairwiseDisjoint_sum_indicator {f : LocallyConstant X M}
    (hf : HasCompactSupport f) :
    ∃ (s : Finset M) (K : M → CompactOpens X), 0 ∉ s ∧
      (s : Set M).PairwiseDisjoint (fun m => (K m : Set X)) ∧
      ⇑f = ∑ m ∈ s, (K m : Set X).indicator fun _ => m := by
  classical
  -- The nonzero part of the fibre over `m` is open, and compact as a closed part of the support.
  let K : M → CompactOpens X := fun m =>
    ⟨⟨f ⁻¹' {m} ∩ support f, hf.of_isClosed_subset
      ((f.isLocallyConstant.isClopen_fiber m).isClosed.inter f.isClopen_support.isClosed)
      (inter_subset_right.trans (subset_tsupport f))⟩,
      (f.isLocallyConstant.isClopen_fiber m).isOpen.inter f.isClopen_support.isOpen⟩
  have hK (m : M) (x : X) : x ∈ (K m : Set X) ↔ f x = m ∧ f x ≠ 0 := Iff.rfl
  refine ⟨(finite_range_of_hasCompactSupport hf).toFinset.erase 0, K, Finset.notMem_erase 0 _,
    fun m _ m' _ hmm' => disjoint_left.2 fun x hx hx' => hmm' ?_, funext fun x => ?_⟩
  · exact ((hK m x).1 hx).1.symm.trans ((hK m' x).1 hx').1
  rw [Finset.sum_apply]
  by_cases hx : f x = 0
  · exact hx.trans (Finset.sum_eq_zero fun m _ => Set.indicator_of_notMem (by simp [hK, hx]) _).symm
  rw [Finset.sum_eq_single_of_mem (f x) (by simp [hx]) fun m _ hm =>
    Set.indicator_of_notMem (by simp [hK, Ne.symm hm]) _]
  exact (Set.indicator_of_mem ((hK _ x).2 ⟨rfl, hx⟩) _).symm

/-- In a Hausdorff space, `C_c^∞(X, M)` is spanned by the indicators `1_K • m` of compact open
sets `K`, which are clopen. -/
theorem compactlySupported_eq_span [T2Space X] :
    compactlySupported R X M = Submodule.span R
      (range fun p : CompactOpens X × M => (const X p.2).indicator p.1.toClopens.isClopen) := by
  refine le_antisymm (fun f hf => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨s, K, -, -, hfs⟩ := exists_pairwiseDisjoint_sum_indicator hf
    have hf' : f = ∑ m ∈ s, (const X m).indicator (K m).toClopens.isClopen :=
      coe_injective (by rw [hfs]; exact (map_sum (coeFnAddMonoidHom (X := X) (Y := M))
        (fun m => (const X m).indicator (K m).toClopens.isClopen) s).symm)
    rw [hf']
    exact Submodule.sum_mem _ fun m _ => Submodule.subset_span ⟨(K m, m), rfl⟩
  · rintro _ ⟨⟨K, m⟩, rfl⟩
    exact indicator_mem_compactlySupported _ _ K.isCompact

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

section Group

variable [Group G] [TopologicalSpace G]

/-- **Two-sided uniform local constancy.** A locally constant function with compact support on a
locally profinite group (a weakly locally compact nonarchimedean group) is invariant under left
and right translation by some compact open subgroup. -/
theorem exists_isCompact_openSubgroup_forall_mul_eq [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] [Zero M] {f : LocallyConstant G M} (hf : HasCompactSupport f) :
    ∃ U : OpenSubgroup G, IsCompact (U : Set G) ∧
      ∀ u ∈ U, ∀ x, f (u * x) = f x ∧ f (x * u) = f x := by
  -- Left translation invariance of `f` is right translation invariance of `x ↦ f x⁻¹`.
  have hl := TauCeti.isOpen_rightTranslationStabilizer_of_hasCompactSupport
    (f.isLocallyConstant.comp_continuous continuous_inv) (hf.comp_homeomorph (Homeomorph.inv G))
  have hr := TauCeti.isOpen_rightTranslationStabilizer_of_hasCompactSupport f.isLocallyConstant hf
  obtain ⟨U, hUc, hUS⟩ := NonarchimedeanGroup.isCoinitial_isCompact_openSubgroup
    (⟨TauCeti.rightTranslationStabilizer (fun x => f x⁻¹) ⊓
      TauCeti.rightTranslationStabilizer f, hl.inter hr⟩ : OpenSubgroup G)
  refine ⟨U, hUc, fun u hu x => ⟨?_,
    TauCeti.mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 (hUS hu)).2 x⟩⟩
  simpa using TauCeti.mem_rightTranslationStabilizer.1 (Subgroup.mem_inf.1 (hUS (inv_mem hu))).1 x⁻¹

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The `R`-module `C_c^∞(G, M)^U` of locally constant functions with compact support that are
invariant under right translation by a subgroup `U`, that is, constant on each left coset
`g U`. -/
def compactlySupportedRightInvariant (U : Subgroup G) : Submodule R (LocallyConstant G M) where
  carrier := {f | HasCompactSupport f ∧ ∀ u ∈ U, ∀ x, f (x * u) = f x}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun u hu x => by simp [hf.2 u hu x, hg.2 u hu x]⟩
  zero_mem' := ⟨HasCompactSupport.zero, fun _ _ _ => rfl⟩
  smul_mem' c f hf := ⟨hf.1.mono (support_const_smul_subset c f), fun u hu x => by
    simp [hf.2 u hu x]⟩

@[simp]
theorem mem_compactlySupportedRightInvariant {U : Subgroup G} {f : LocallyConstant G M} :
    f ∈ compactlySupportedRightInvariant R M U ↔
      HasCompactSupport f ∧ ∀ u ∈ U, ∀ x, f (x * u) = f x :=
  Iff.rfl

/-- Right `U`-invariant test functions are test functions. -/
theorem compactlySupportedRightInvariant_le_compactlySupported (U : Subgroup G) :
    compactlySupportedRightInvariant R M U ≤ compactlySupported R G M :=
  fun _ hf => hf.1

variable [IsTopologicalGroup G]

/-- The function on `G ⧸ U` through which a right `U`-invariant test function factors. -/
private def quotientLift {U : Subgroup G} (f : compactlySupportedRightInvariant R M U) :
    G ⧸ U → M :=
  Quotient.lift (f : G → M) fun x y hxy => by
    simpa using ((mem_compactlySupportedRightInvariant.1 f.2).2 _
      (QuotientGroup.leftRel_apply.1 hxy) x).symm

/-- **Right-invariant test functions are finitely supported functions on `G ⧸ U`.** For a compact
open subgroup `U` of `G`, factoring through the quotient map identifies the right
`U`-invariant elements of `C_c^∞(G, M)` with the finitely supported functions on `G ⧸ U`. -/
noncomputable def compactlySupportedRightInvariantEquiv (U : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) :
    compactlySupportedRightInvariant R M (U : Subgroup G) ≃ₗ[R] G ⧸ (U : Subgroup G) →₀ M where
  toFun f := Finsupp.ofSupportFinite (quotientLift f) <| by
    -- The support lies in the image of the compact support, which is finite in `G ⧸ U`.
    refine ((f.2.1.isCompact.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
    rintro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, subset_tsupport _ hq, rfl⟩
  invFun φ := ⟨⟨fun x => φ x,
      (IsLocallyConstant.of_discrete _).comp_continuous QuotientGroup.continuous_mk⟩,
    hasCompactSupport_iff_isCompact_support.2 <| by
      -- The support is `S * U` for the finite set `S` of representatives of the support of `φ`.
      have hS : support (fun x : G => φ x) =
          Quotient.out '' (φ.support : Set (G ⧸ (U : Subgroup G))) *
            ((U : Subgroup G) : Set G) := by
        rw [← QuotientGroup.preimage_image_mk_eq_mul, image_image]
        ext x
        simp
      exact hS ▸ (φ.support.finite_toSet.image _).isCompact.mul hU,
    fun u hu x => by simp [QuotientGroup.mk_mul_of_mem x hu]⟩
  -- At a coset `x U`, both maps evaluate the lifted function at its representative `x`, which
  -- `Quotient.lift` does by definition.
  map_add' f g := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_smul' c f := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  left_inv f := rfl
  right_inv φ := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

/-- The finitely supported function attached to a right `U`-invariant test function `f` takes the
value `f x` at the coset `x U`. -/
@[simp]
theorem compactlySupportedRightInvariantEquiv_apply_mk {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (f : compactlySupportedRightInvariant R M (U : Subgroup G))
    (x : G) : compactlySupportedRightInvariantEquiv U hU f x = (f : LocallyConstant G M) x :=
  (rfl)

/-- The test function attached to a finitely supported function `φ` on `G ⧸ U` takes the value
`φ (x U)` at `x`. -/
@[simp]
theorem compactlySupportedRightInvariantEquiv_symm_apply {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (φ : G ⧸ (U : Subgroup G) →₀ M) (x : G) :
    ((compactlySupportedRightInvariantEquiv (R := R) U hU).symm φ : LocallyConstant G M) x =
      φ x :=
  (rfl)

end Group

end LocallyConstant
