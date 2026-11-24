/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.LocallyConstant.CompactSupport
import TauCeti.Topology.Algebra.Group.LocallyConstant
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact

/-!
# Locally constant functions with compact support on a topological group

On a topological group `G`, a locally constant function with compact support, an element of
`C_c^∞(G, M) = LocallyConstant.compactlySupported R G M`, is uniformly locally constant: it is
invariant under left and right translation by an open subgroup, which can be taken compact when `G`
is weakly locally compact and nonarchimedean, in particular when `G` is locally profinite
(`LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq`). For a compact open subgroup `U`,
the test functions invariant under right translation by `U` are the finitely supported functions on
`G ⧸ U` (`LocallyConstant.compactlySupportedRightInvariantEquiv`).

## Main definitions

* `LocallyConstant.compactlySupportedRightInvariant R M U`: the right `U`-invariant elements of
  `C_c^∞(G, M)`.
* `LocallyConstant.compactlySupportedRightInvariantEquiv`: for `U` compact open, the
  identification of the right `U`-invariant test functions with `G ⧸ U →₀ M`.

## Main results

* `LocallyConstant.exists_isCompact_openSubgroup_forall_mul_eq`: on a weakly locally compact
  nonarchimedean group, every test function is left and right invariant under some compact open
  subgroup.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §1.1, Lemma 1, and §1.2, pp. 7–8.
* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.1, p. 25.
-/

public section

open Function Set
open scoped Pointwise

namespace LocallyConstant

variable {R G M : Type*} [Group G] [TopologicalSpace G]

/-- **Two-sided uniform local constancy.** A locally constant function with compact support on a
weakly locally compact nonarchimedean group (in particular, on a locally profinite group) is
invariant under left and right translation by some compact open subgroup. -/
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
  fun _ hf => mem_compactlySupported.2 hf.1

/-- The function on `G ⧸ U` through which a right `U`-invariant test function factors. -/
private def quotientLift {U : Subgroup G} (f : compactlySupportedRightInvariant R M U) :
    G ⧸ U → M :=
  Quotient.lift (f : G → M) fun x y hxy => by
    simpa using ((mem_compactlySupportedRightInvariant.1 f.property).2 _
      (QuotientGroup.leftRel_apply.1 hxy) x).symm

/-- `quotientLift f` takes the value `f x` at the coset `x U`; this is how `Quotient.lift`
computes on `Quotient.mk`. -/
private theorem quotientLift_mk {U : Subgroup G} (f : compactlySupportedRightInvariant R M U)
    (x : G) : quotientLift f x = (f : LocallyConstant G M) x :=
  rfl

variable [IsTopologicalGroup G]

/-- **Right-invariant test functions are finitely supported functions on `G ⧸ U`.** For a compact
open subgroup `U` of `G`, factoring through the quotient map identifies the right
`U`-invariant elements of `C_c^∞(G, M)` with the finitely supported functions on `G ⧸ U`. -/
noncomputable def compactlySupportedRightInvariantEquiv (U : OpenSubgroup G)
    (hU : IsCompact (U : Set G)) :
    compactlySupportedRightInvariant R M (U : Subgroup G) ≃ₗ[R] G ⧸ (U : Subgroup G) →₀ M where
  toFun f := Finsupp.ofSupportFinite (quotientLift f) <| by
    -- The support lies in the image of the compact support, which is finite in `G ⧸ U`.
    refine ((f.property.1.isCompact.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
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
  -- At a coset `x U`, both maps evaluate the lifted function at its representative `x`.
  map_add' f g := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Finsupp.ofSupportFinite_coe, quotientLift_mk]
  map_smul' c f := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Finsupp.ofSupportFinite_coe, quotientLift_mk]
  left_inv f := Subtype.ext <| LocallyConstant.ext fun x => by
    simp [Finsupp.ofSupportFinite_coe, quotientLift_mk]
  right_inv φ := Finsupp.ext fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    simp [Finsupp.ofSupportFinite_coe, quotientLift_mk]

/-- The finitely supported function attached to a right `U`-invariant test function `f` takes the
value `f x` at the coset `x U`. -/
@[simp]
theorem compactlySupportedRightInvariantEquiv_apply_mk {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (f : compactlySupportedRightInvariant R M (U : Subgroup G))
    (x : G) : compactlySupportedRightInvariantEquiv U hU f x = (f : LocallyConstant G M) x := by
  simp [compactlySupportedRightInvariantEquiv, Finsupp.ofSupportFinite_coe, quotientLift_mk]

/-- The test function attached to a finitely supported function `φ` on `G ⧸ U` takes the value
`φ (x U)` at `x`. -/
@[simp]
theorem compactlySupportedRightInvariantEquiv_symm_apply {U : OpenSubgroup G}
    (hU : IsCompact (U : Set G)) (φ : G ⧸ (U : Subgroup G) →₀ M) (x : G) :
    ((compactlySupportedRightInvariantEquiv (R := R) U hU).symm φ : LocallyConstant G M) x =
      φ x := by
  simp [compactlySupportedRightInvariantEquiv]

end LocallyConstant
