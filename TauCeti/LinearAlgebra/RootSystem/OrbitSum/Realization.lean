/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.RootSystem.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.Dominance
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance.Basic
import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Cone

/-!
# Orbit-sum realizations of a root-pairing automorphism

When an automorphism `σ` of a root system `P` permutes `b.support` for a base `b`, a weight is
fixed by `σ` iff its `b.toWeightBasis` coordinates are constant along the `σ`-cycles of `b.support`,
giving a basis `RootPairing.Base.fixedSubmoduleBasis` of `LinearMap.fixedSubmodule σ.weightMap`.
When `ι` is finite, its basis vectors are the simple-orbit sums `P.orbitSum σ j` (`j ∈ b.support`),
so `RootPairing.foldedRootEmb P σ` spans the fixed submodule and the simple-orbit sums are linearly
independent and positively generate all positive orbit sums.

`RootPairing.OrbitSumRealization P b σ` bundles a reduced crystallographic root system on
`LinearMap.fixedSubmodule σ.weightMap` and its linear dual, indexed by `P.foldedIndices σ`, paired
by evaluation, with orbit-sum roots and simple-orbit base. Over a characteristic-zero domain it is
unique (`ext`, `Subsingleton`); when `σ` stabilizes `b` over a characteristic-zero ring, positivity
in `F.base` matches `b`. We also construct `OrbitSumRealization.one` (`equivOne`) and transport
along intertwining based equivalences (`map`, `mapEquiv`, `equivOfMap`).

The folded integral structures are the invariant parts of the original ones: when `σ` stabilizes
`b.support`, a `σ`-fixed vector lies in the positive root monoid, respectively the root lattice, of
`b` exactly when it lies in that of `F` (`OrbitSumRealization.coe_mem_posRootCone_iff`,
`OrbitSumRealization.coe_mem_rootSpan_int_iff`). So integral root dominance between fixed vectors
is folded integral dominance (`OrbitSumRealization.rootLE_coe_iff`), with no integrality of the
endpoints, and the `F.base`-coordinate of a fixed vector at a simple-orbit sum `β_O` is its
`b`-coordinate at any member of `O` (`OrbitSumRealization.base_toWeightBasis_repr`). These rest on
the regrouping of fixed natural and integral combinations of simple roots in
`TauCeti.LinearAlgebra.RootSystem.OrbitSum.Cone`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pp. 1–3.
-/

public section

namespace RootPairing

open Finset Function Set TauCeti

/-! ### Simple-orbit basis and folded root embedding -/

section FixedSubmoduleBasis

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The canonical embedding of `P.foldedIndices σ` into `LinearMap.fixedSubmodule σ.weightMap`. -/
def foldedRootEmb (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut) :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap where
  toFun u := ⟨(u : M),
    let ⟨r, hr⟩ := mem_foldedIndices.mp u.property; hr ▸ P.orbitSum_mem_fixedSubmodule σ r⟩
  inj' _ _ h := Subtype.ext (Subtype.mk.inj h)

@[simp] theorem coe_foldedRootEmb_apply (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)
    (u : P.foldedIndices σ) : (P.foldedRootEmb σ u : M) = (u : M) := by rfl

namespace Base

variable {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base) {σ : P.Aut}

private theorem equivFun_comp_weightMap (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    b.toWeightBasis.equivFun.toLinearMap ∘ₗ σ.weightMap =
      (LinearEquiv.funCongrLeft R R (b.supportPerm hσ).symm).toLinearMap ∘ₗ
        b.toWeightBasis.equivFun.toLinearMap := by
  refine b.toWeightBasis.ext fun i ↦ funext fun j ↦ ?_
  classical
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_apply,
    b.toWeightBasis_apply i, Hom.root_weightMap_apply P P i σ.toHom,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  have hπ : P.root (σ.indexEquiv i) = b.toWeightBasis (b.supportPerm hσ i) := by
    rw [← b.coe_supportPerm_apply hσ i, b.toWeightBasis_apply]
  rw [hπ, ← b.toWeightBasis_apply i, Module.Basis.repr_self, Module.Basis.repr_self,
    Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr (b.supportPerm hσ).eq_symm_apply.symm rfl rfl

/-- **The simple-orbit basis of the `σ`-fixed weight submodule**, indexed by the `σ`-cycles of
`b.support`. -/
noncomputable def fixedSubmoduleBasis (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) R
      (LinearMap.fixedSubmodule σ.weightMap) :=
  let qCongr : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) :=
    Quotient.congr (_root_.Equiv.refl _) fun _ _ ↦ Equiv.Perm.sameCycle_inv
  ((Equiv.Perm.permutationFixedBasis (R := R) (b.supportPerm hσ)⁻¹).reindex qCongr).map
    (b.toWeightBasis.equivFun.fixedSubmoduleCongr (b.equivFun_comp_weightMap hσ)).symm

/-- The coordinate of a `σ`-fixed vector on the simple orbit of `j` is its `b.toWeightBasis`
coordinate at `j`. -/
@[simp] theorem fixedSubmoduleBasis_repr (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (x : LinearMap.fixedSubmodule σ.weightMap) (j : b.support) :
    (b.fixedSubmoduleBasis hσ).repr x (Quotient.mk _ j) = b.toWeightBasis.repr (x : M) j := by
  let qCongr : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) :=
    Quotient.congr (_root_.Equiv.refl b.support) fun _ _ ↦ Equiv.Perm.sameCycle_inv
  have hq : qCongr.symm (Quotient.mk _ j) = Quotient.mk _ j := rfl
  simp only [fixedSubmoduleBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Module.Basis.repr_reindex_apply]
  rw [hq, Equiv.Perm.permutationFixedBasis_repr]
  exact congrFun (LinearEquiv.fixedSubmoduleCongr_apply b.toWeightBasis.equivFun
    (b.equivFun_comp_weightMap hσ) x) j

/-- The coordinate of a `σ`-fixed vector on a simple cycle `O` is its `b.toWeightBasis` coordinate
at `O.out`. -/
theorem fixedSubmoduleBasis_repr_out (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (x : LinearMap.fixedSubmodule σ.weightMap)
    (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
    (b.fixedSubmoduleBasis hσ).repr x O = b.toWeightBasis.repr (x : M) O.out := by
  simpa only [Quotient.out_eq] using b.fixedSubmoduleBasis_repr hσ x O.out

section Finite

variable [Finite ι]

/-- Each basis vector of `fixedSubmoduleBasis` at a cycle `O` is `P.orbitSum σ O.out`. -/
theorem coe_fixedSubmoduleBasis_out (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
    ((b.fixedSubmoduleBasis hσ O) : M) = P.orbitSum σ (O.out : ι) := by
  classical
  refine b.toWeightBasis.equivFun.injective (funext fun j ↦ ?_)
  rw [Module.Basis.equivFun_apply, ← b.fixedSubmoduleBasis_repr hσ (b.fixedSubmoduleBasis hσ O) j,
    Module.Basis.repr_self, Finsupp.single_apply, orbitSum_def, map_sum, Finset.sum_apply]
  have hmem : (j : ι) ∈ P.orbitIndices σ (O.out : ι) ↔
      Quotient.mk (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) j = O := by
    rw [mem_orbitIndices, ← b.sameCycle_supportPerm_iff hσ]
    exact ⟨fun h ↦ (Quotient.sound h.symm).trans (Quotient.out_eq O),
      fun h ↦ (Quotient.exact (h.trans (Quotient.out_eq O).symm)).symm⟩
  have hterm (k : ι) (hk : k ∈ P.orbitIndices σ (O.out : ι)) :
      b.toWeightBasis.equivFun (P.root k) j = if k = (j : ι) then 1 else 0 := by
    have hks : k ∈ b.support := b.orbitIndices_subset_support hσ O.out.property hk
    have hbk : P.root k = b.toWeightBasis ⟨k, hks⟩ := (b.toWeightBasis_apply ⟨k, hks⟩).symm
    rw [Module.Basis.equivFun_apply, hbk, Module.Basis.repr_self, Finsupp.single_apply]
    exact if_congr Subtype.ext_iff rfl rfl
  rw [Finset.sum_congr rfl fun k hk ↦ hterm k hk, Finset.sum_ite_eq']
  exact if_congr (eq_comm.trans hmem.symm) rfl rfl

/-- The `fixedSubmoduleBasis` vector at the cycle of `j : b.support` is `P.orbitSum σ j`. -/
@[simp] theorem coe_fixedSubmoduleBasis_mk (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (j : b.support) : ((b.fixedSubmoduleBasis hσ (Quotient.mk _ j)) : M) = P.orbitSum σ j := by
  let O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) := Quotient.mk _ j
  exact (b.coe_fixedSubmoduleBasis_out hσ O).trans (orbitSum_eq_of_mem (mem_orbitIndices.mpr
    ((b.sameCycle_supportPerm_iff hσ).mp (Quotient.exact (Quotient.out_eq O))).symm))

/-- When `σ` stabilizes `b.support`, `P.foldedRootEmb σ` spans the `σ`-fixed weight submodule. -/
theorem span_foldedRootEmb_eq_top (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    Submodule.span R (range (P.foldedRootEmb σ)) = ⊤ := by
  rw [eq_top_iff, ← (b.fixedSubmoduleBasis hσ).span_eq]
  exact Submodule.span_mono fun _ ⟨O, hO⟩ ↦ hO ▸ ⟨⟨P.orbitSum σ (O.out : ι),
    P.orbitSum_mem_foldedIndices σ _⟩, Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm⟩

/-- When `σ` stabilizes `b.support`, the distinct simple-orbit sums are linearly independent in
`LinearMap.fixedSubmodule σ.weightMap`. -/
theorem linearIndepOn_foldedRootEmb (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    LinearIndepOn R (P.foldedRootEmb σ)
      {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact linearIndepOn_iff'.mpr fun _ _ _ _ _ _ ↦ Subsingleton.elim _ _
  · let idxMap : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) → P.foldedIndices σ :=
      fun O ↦ ⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩
    have hcomp : P.foldedRootEmb σ ∘ idxMap = b.fixedSubmoduleBasis hσ :=
      funext fun O ↦ Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm
    have hli : LinearIndependent R (P.foldedRootEmb σ ∘ idxMap) :=
      hcomp.symm ▸ (b.fixedSubmoduleBasis hσ).linearIndependent
    have hrange : range idxMap =
        {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
      ext u
      refine ⟨fun ⟨O, hO⟩ ↦ hO ▸ ⟨O.out, O.out.property, rfl⟩, fun ⟨j, hj, hju⟩ ↦ ?_⟩
      let O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) := Quotient.mk _ ⟨j, hj⟩
      have hsc := (b.sameCycle_supportPerm_iff hσ).mp (Quotient.exact (Quotient.out_eq O))
      exact ⟨O, Subtype.ext ((orbitSum_eq_of_mem (mem_orbitIndices.mpr hsc.symm)).trans hju)⟩
    exact hrange ▸ (linearIndepOn_range_iff (Injective.of_comp hli.injective) _).mpr hli

/-- Over a characteristic-zero ring, when `σ` stabilizes `b.support`, the orbit sum of every
`b`-positive root belongs to the additive submonoid generated by the simple-orbit sums. -/
theorem foldedRootEmb_orbitSum_mem_closure_of_isPos [CharZero R]
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {r : ι} (hr : b.IsPos r) :
    P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ ∈
      AddSubmonoid.closure (P.foldedRootEmb σ ''
        {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)}) := by
  classical
  set x := P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hr)
  have hrepr (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
      (b.fixedSubmoduleBasis hσ).repr x O = (c (O.out : ι) : R) := by
    rw [b.fixedSubmoduleBasis_repr_out hσ x O, ← Module.Basis.equivFun_apply,
      coe_foldedRootEmb_apply, Subtype.coe_mk]
    have hsum : P.orbitSum σ r = ∑ j : b.support, c (j : ι) • b.toWeightBasis j :=
      hc.trans ((Finset.sum_coe_sort b.support _).symm.trans
        (Finset.sum_congr rfl fun j _ ↦ by rw [b.toWeightBasis_apply]))
    rw [hsum, map_sum, Finset.sum_apply, Finset.sum_eq_single O.out]
    · rw [map_nsmul, Pi.smul_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, nsmul_eq_mul, mul_one]
    · exact fun j _ hjO ↦ by
        rw [map_nsmul, Pi.smul_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne hjO.symm, nsmul_zero]
    · exact fun hnot ↦ absurd (Finset.mem_univ O.out) hnot
  rw [← (b.fixedSubmoduleBasis hσ).sum_repr x]
  refine sum_mem fun O _ ↦ ?_
  rw [hrepr O, Nat.cast_smul_eq_nsmul]
  refine nsmul_mem (AddSubmonoid.subset_closure ?_) (c (O.out : ι))
  exact ⟨⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩, ⟨O.out, O.out.property, rfl⟩,
    Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm⟩

end Finite

end Base

end FixedSubmoduleBasis

/-! ### Bundled orbit-sum realizations -/

/-- An **orbit-sum realization** of `(P, b, σ)` bundles a reduced crystallographic root system on
`LinearMap.fixedSubmodule σ.weightMap` and its `R`-linear dual, indexed by `P.foldedIndices σ`,
paired by evaluation, whose roots are the orbit sums and whose simple roots are the simple-orbit
sums. -/
structure OrbitSumRealization {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι]
    (b : P.Base) (σ : P.Aut) where
  /-- The root pairing on the `σ`-fixed submodule and its linear dual. -/
  pairing : RootPairing (P.foldedIndices σ) R (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- Its simple base. -/
  base : pairing.Base
  /-- Both the folded roots and folded coroots span. -/
  rootSystem : pairing.IsRootSystem
  /-- No proportional folded roots except a root and its negative. -/
  reduced : pairing.IsReduced
  /-- All folded root-coroot pairings are integers. -/
  crystallographic : pairing.IsCrystallographic
  /-- The perfect pairing is evaluation against the fixed-space dual. -/
  evaluation : ∀ x y, pairing.toLinearMap x y = y x
  /-- Each folded root is its literal orbit-sum vector in the ambient space `M`. -/
  root_eq : ∀ i, (pairing.root i : M) = (i : M)
  /-- Simple roots of `base` are precisely the orbit sums of simple roots of `b`. -/
  base_eq : ∀ i, i ∈ base.support ↔ ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

attribute [instance] OrbitSumRealization.rootSystem OrbitSumRealization.reduced
  OrbitSumRealization.crystallographic

namespace OrbitSumRealization

section Basic

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} (F : P.OrbitSumRealization b σ)

theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (y : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x y = y x := F.evaluation x y
@[simp] theorem toLinearMap_eq_eval :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) :=
  LinearMap.ext₂ F.evaluation
@[simp] theorem coe_root (i : P.foldedIndices σ) : (F.pairing.root i : M) = (i : M) := F.root_eq i
@[simp] theorem root_orbitSum (j : ι) :
    F.pairing.root ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ =
      ⟨P.orbitSum σ j, P.orbitSum_mem_fixedSubmodule σ j⟩ := Subtype.ext (F.coe_root _)
theorem coroot'_apply (i : P.foldedIndices σ) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' i x = F.pairing.coroot i x := F.evaluation x (F.pairing.coroot i)
@[simp] theorem mem_support_base_iff {i : P.foldedIndices σ} :
    i ∈ F.base.support ↔ ∃ j ∈ b.support, P.orbitSum σ j = (i : M) := F.base_eq i
theorem orbitSum_mem_support_base {j : ι} (hj : j ∈ b.support) :
    ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ ∈ F.base.support :=
  F.mem_support_base_iff.mpr ⟨j, hj, rfl⟩

end Basic

/-! ### Uniqueness -/

section Uniqueness

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

/-- Any two orbit-sum realizations of `(P, b, σ)` over a characteristic-zero domain have the same
underlying root pairing. -/
theorem pairing_eq (F₁ F₂ : P.OrbitSumRealization b σ) : F₁.pairing = F₂.pairing :=
  IsRootSystem.ext (F₁.toLinearMap_eq_eval.trans F₂.toLinearMap_eq_eval.symm)
    (DFunLike.ext _ _ fun i ↦ Subtype.ext ((F₁.coe_root i).trans (F₂.coe_root i).symm))

/-- **Uniqueness of an orbit-sum realization** over a domain of characteristic zero. -/
@[ext] theorem ext (F₁ F₂ : P.OrbitSumRealization b σ) : F₁ = F₂ := by
  have hP := pairing_eq F₁ F₂
  cases F₁ with | mk p₁ b₁ _ _ _ _ _ bs₁ =>
  cases F₂ with | mk p₂ b₂ _ _ _ _ _ bs₂ =>
  subst hP; congr
  exact Base.ext (Finset.ext fun i ↦ (bs₁ i).trans (bs₂ i).symm)

instance : Subsingleton (P.OrbitSumRealization b σ) := ⟨ext⟩

end Uniqueness

/-! ### Integral cones, root lattices and dominance -/

section Cone

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} (F : P.OrbitSumRealization b σ)

/-- The ambient vectors of the simple roots of `F.base` are exactly the simple-orbit sums. -/
theorem image_coe_root_support :
    Subtype.val '' (F.pairing.root '' F.base.support) = P.orbitSum σ '' b.support := by
  ext x
  simp only [Set.image_image, Set.mem_image, Finset.mem_coe, F.coe_root, F.mem_support_base_iff]
  refine ⟨fun ⟨u, ⟨j, hj, hju⟩, hux⟩ ↦ ⟨j, hj, hju.trans hux⟩, fun ⟨j, hj, hjx⟩ ↦ ?_⟩
  exact ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩, ⟨j, hj, rfl⟩, hjx⟩

/-- The positive root monoid of `F.base`, viewed in `M`, is the monoid generated by the
simple-orbit sums. -/
theorem map_posRootCone :
    (posRootCone F.pairing F.base).map (LinearMap.fixedSubmodule σ.weightMap).subtype =
      AddSubmonoid.closure (P.orbitSum σ '' b.support) := by
  rw [posRootCone_def, AddMonoidHom.map_mclosure, Submodule.coe_subtype, image_coe_root_support]

/-- The root lattice of `F.pairing`, viewed in `M`, is the group generated by the simple-orbit
sums. -/
theorem map_rootSpan_int :
    (F.pairing.rootSpan ℤ).map
        ((LinearMap.fixedSubmodule σ.weightMap).subtype.restrictScalars ℤ) =
      Submodule.span ℤ (P.orbitSum σ '' b.support) := by
  rw [rootSpan, ← F.base.span_int_root_support, Submodule.map_span, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype, image_coe_root_support]

/-- **The invariant positive root monoid is the folded one.** When `σ` permutes the simple roots
of `b`, a `σ`-fixed vector lies in the positive root monoid `Q⁺` of `b` exactly when it lies in the
positive root monoid of `F.base`, that is, when it is a natural combination of the simple-orbit
sums. -/
theorem coe_mem_posRootCone_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} :
    (x : M) ∈ posRootCone P b ↔ x ∈ posRootCone F.pairing F.base := by
  rw [mem_posRootCone_iff_mem_closure_orbitSum hσ x.property, ← F.map_posRootCone]
  exact AddSubmonoid.mem_map_iff_mem Subtype.val_injective

/-- **The invariant root lattice is the folded one.** When `σ` permutes the simple roots of `b`,
a `σ`-fixed vector lies in the root lattice of `P` exactly when it lies in the root lattice of
`F.pairing`, that is, when it is an integral combination of the simple-orbit sums. -/
theorem coe_mem_rootSpan_int_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} :
    (x : M) ∈ P.rootSpan ℤ ↔ x ∈ F.pairing.rootSpan ℤ := by
  rw [mem_rootSpan_int_iff_mem_span_orbitSum hσ x.property, ← F.map_rootSpan_int, ← SetLike.mem_coe,
    Submodule.map_coe]
  exact Subtype.val_injective.mem_set_image

/-- **Integral root dominance between fixed vectors is folded dominance.** When `σ` permutes the
simple roots of `b`, two `σ`-fixed vectors are comparable for `b` exactly when they are comparable
for `F.base`. No integrality of the endpoints is needed, since only their difference is tested. -/
theorem rootLE_coe_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x y : LinearMap.fixedSubmodule σ.weightMap} :
    P.rootLE b x y ↔ F.pairing.rootLE F.base x y := by
  rw [rootLE_iff_sub_mem_posRootCone, rootLE_iff_sub_mem_posRootCone, ← Submodule.coe_sub,
    F.coe_mem_posRootCone_iff hσ]

/-- **The folded simple-root coordinates of a fixed vector.** When `σ` permutes the simple roots
of `b`, the coordinate of a `σ`-fixed vector at the simple root `β_O` of `F.base` is its
`b`-coordinate at any simple root `αⱼ` with `j ∈ O`. So the unique expansion of a fixed vector in
the simple-orbit sums has, at `β_O`, the common `b`-coordinate of the members of `O`. -/
theorem base_toWeightBasis_repr [P.IsRootSystem]
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (x : LinearMap.fixedSubmodule σ.weightMap)
    {j : ι} (hj : j ∈ b.support) :
    F.base.toWeightBasis.repr x ⟨_, F.orbitSum_mem_support_base hj⟩ =
      b.toWeightBasis.repr (x : M) ⟨j, hj⟩ := by
  classical
  -- Compare the two coordinate functionals on the basis `F.base.toWeightBasis`.
  suffices F.base.toWeightBasis.coord ⟨_, F.orbitSum_mem_support_base hj⟩ =
      (b.toWeightBasis.coord ⟨j, hj⟩).comp (LinearMap.fixedSubmodule σ.weightMap).subtype from
    LinearMap.congr_fun this x
  refine F.base.toWeightBasis.ext fun w ↦ ?_
  obtain ⟨k, hk, hkw⟩ := F.mem_support_base_iff.mp w.property
  have hsub := b.orbitIndices_subset_support hσ hk
  have hw : w = ⟨_, F.orbitSum_mem_support_base hj⟩ ↔ j ∈ P.orbitIndices σ k := by
    rw [Subtype.ext_iff, Subtype.ext_iff, ← hkw]
    exact b.orbitSum_eq_orbitSum_iff_of_mem_support hσ hk hj
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hw]
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, Base.toWeightBasis_apply, F.coe_root,
    ← hkw, orbitSum_def, Module.Basis.coord_apply, map_sum]
  have hcoord (i : ι) (hi : i ∈ P.orbitIndices σ k) :
      b.toWeightBasis.repr (P.root i) ⟨j, hj⟩ = if i = j then 1 else 0 := by
    rw [← b.toWeightBasis_apply ⟨i, hsub hi⟩, Module.Basis.repr_self, Finsupp.single_apply]
    exact if_congr Subtype.ext_iff rfl rfl
  rw [Finset.sum_congr rfl hcoord, Finset.sum_ite_eq']

end Cone

/-! ### Positive roots -/

section Positive

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} (F : P.OrbitSumRealization b σ)

/-- **Positivity of an orbit sum in `F.base` matches positivity in `b`** when `σ` stabilizes
`b.support` over a characteristic-zero ring. -/
theorem isPos_orbitSum_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (j : ι) :
    F.base.IsPos ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ ↔ b.IsPos j := by
  have hpos {k : ι} (hk : b.IsPos k) :
      F.base.IsPos ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := by
    set u : P.foldedIndices σ := ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩
    by_contra hnot
    have hneg_pos : F.pairing.reflectionPerm u u ∈ posRoots F.pairing F.base :=
      (mem_posRoots _ _ _).mpr ((isPos_reflectionPerm_self_iff_mem_negRoots F.pairing F.base u).mpr
        ((mem_negRoots _ _ _).mpr hnot))
    have hm := (F.coe_mem_posRootCone_iff hσ).mpr
      (root_mem_posRootCone_of_mem_posRoots F.pairing F.base hneg_pos)
    rw [root_reflectionPerm, reflection_apply_self, Submodule.coe_neg, F.coe_root] at hm
    exact orbitSum_ne_zero hσ k (eq_zero_of_add_eq_zero_of_mem_posRootCone P b
      (orbitSum_mem_posRootCone hσ hk) hm (add_neg_cancel _))
  refine ⟨fun h ↦ ?_, hpos⟩
  by_contra hnot
  have hneg_pos : b.IsPos (P.reflectionPerm j j) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr ((mem_negRoots P b j).mpr hnot)
  have h₁ : P.orbitSum σ j ∈ posRootCone P b := by
    simpa [F.coe_root] using (F.coe_mem_posRootCone_iff hσ).mpr
      (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr h))
  have h₂ : -P.orbitSum σ j ∈ posRootCone P b := by
    simpa [orbitSum_reflectionPerm_self] using orbitSum_mem_posRootCone hσ hneg_pos
  exact orbitSum_ne_zero hσ j
    (eq_zero_of_add_eq_zero_of_mem_posRootCone P b h₁ h₂ (add_neg_cancel _))

/-- **Over a characteristic-zero ring, when `σ` stabilizes `b.support`, a folded root is
`F.base`-positive if and only if it is the orbit sum of a `b`-positive root.** -/
theorem isPos_iff_exists_isPos (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (u : P.foldedIndices σ) :
    F.base.IsPos u ↔ ∃ j, b.IsPos j ∧ P.orbitSum σ j = (u : M) := by
  obtain ⟨j, hj⟩ := mem_foldedIndices.mp u.property
  have hu : u = ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ := Subtype.ext hj.symm
  refine ⟨fun h ↦ ⟨j, (F.isPos_orbitSum_iff hσ j).mp (hu ▸ h), hj⟩, fun ⟨k, hk, hku⟩ ↦ ?_⟩
  have huk : u = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := Subtype.ext hku.symm
  exact huk ▸ (F.isPos_orbitSum_iff hσ k).mpr hk

end Positive

/-! ### Identity realization -/

section One

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι]

private noncomputable def foldedIndicesOneEquiv : ι ≃ P.foldedIndices 1 :=
  _root_.Equiv.ofBijective (fun i ↦ ⟨P.root i, P.foldedIndices_one ▸ Set.mem_range_self i⟩)
    ⟨fun _ _ h ↦ P.root.injective (congrArg Subtype.val h),
      fun ⟨_, hx⟩ ↦ let ⟨i, hi⟩ := P.foldedIndices_one ▸ hx; ⟨i, Subtype.ext hi⟩⟩

@[simp] private theorem coe_foldedIndicesOneEquiv_apply (i : ι) :
    (foldedIndicesOneEquiv P i : M) = P.root i := by rfl

variable [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base)

/-- **The identity automorphism realizes the original based root system** on
`LinearMap.fixedSubmodule (1 : P.Aut).weightMap` (including the empty root system on `{0}`). -/
noncomputable def one : P.OrbitSumRealization b 1 :=
  let e := foldedIndicesOneEquiv P
  let f := (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
    (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm
  let eqv := P.equivMapDual e f
  { pairing := P.mapDual e f
    base := b.map eqv
    rootSystem := inferInstance
    reduced := eqv.isReduced
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation x y := P.mapDual_toLinearMap_apply e f x y
    root_eq u := by
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.property
      have heu : e i = u := Subtype.ext ((coe_foldedIndicesOneEquiv_apply P i).trans
        ((orbitSum_one P i).symm.trans hi))
      rw [← heu, mapDual_root_apply, _root_.Equiv.symm_apply_apply]
      exact (coe_foldedIndicesOneEquiv_apply P i).symm
    base_eq u := by
      classical
      rw [b.support_map_eq, Finset.mem_image]
      refine ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, ?_⟩, fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext ?_⟩⟩
      · rw [← hju, equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply, orbitSum_one]
      · rw [equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply, ← hju, orbitSum_one] }

/-- The canonical equivalence from `P` to `(OrbitSumRealization.one P b).pairing`. -/
noncomputable def equivOne : P.Equiv (one P b).pairing :=
  P.equivMapDual (foldedIndicesOneEquiv P)
    (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm

-- `Hom.weightMap_one` and `orbitSum_one` simplify the implicit types of `coe_weightMap_equivOne`
-- (`simpNF`), so `@[simp]` is placed on the structural `weightMap`/`weightEquiv`/`indexEquiv` API.
@[simp] theorem weightMap_equivOne : (equivOne P b).weightMap =
    (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm.toLinearMap := by
  dsimp only [equivOne, one]; rw [equivMapDual_weightMap]
theorem coe_weightMap_equivOne (x : M) : ((equivOne P b).weightMap x : M) = x := by
  rw [weightMap_equivOne]; rfl
@[simp] theorem weightEquiv_equivOne : (equivOne P b).weightEquiv =
    (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm := by
  dsimp only [equivOne, one]; rw [equivMapDual_weightEquiv]
theorem weightEquiv_equivOne_symm_apply (x : LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :
    (equivOne P b).weightEquiv.symm x = (x : M) := by rw [weightEquiv_equivOne]; rfl
@[simp] theorem indexEquiv_equivOne (i : ι) :
    (equivOne P b).indexEquiv i = ⟨P.root i, P.foldedIndices_one ▸ Set.mem_range_self i⟩ :=
  Subtype.ext <| by
    dsimp only [equivOne, one]; rw [equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply]
theorem coe_indexEquiv_equivOne (i : ι) : ((equivOne P b).indexEquiv i : M) = P.root i := by simp
theorem indexEquiv_equivOne_orbitSum_eq (i : ι) :
    (equivOne P b).indexEquiv i = ⟨P.orbitSum 1 i, P.orbitSum_mem_foldedIndices 1 i⟩ := by simp
@[simp] theorem indexEquiv_equivOne_symm_root (i : ι) (h : P.root i ∈ P.foldedIndices 1) :
    (equivOne P b).indexEquiv.symm ⟨P.root i, h⟩ = i :=
  (equivOne P b).indexEquiv.injective <| by rw [_root_.Equiv.apply_symm_apply, indexEquiv_equivOne]
theorem indexEquiv_equivOne_symm_orbitSum (i : ι) :
    (equivOne P b).indexEquiv.symm ⟨P.orbitSum 1 i, P.orbitSum_mem_foldedIndices 1 i⟩ = i := by
  simp
@[simp] theorem map_equivOne_base : b.map (equivOne P b) = (one P b).base := by rfl

end One

/-! ### Transport along intertwining equivalences -/

section Map

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι] [Finite ι₂]

private noncomputable def foldedIndicesCongr (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ where
  toFun u := ⟨e.weightEquiv u.val, mem_foldedIndices.mpr <| by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.property
    exact ⟨e.indexEquiv i, (weightMap_orbitSum e
      (e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw) i).symm.trans
      (congrArg e.weightMap hi)⟩⟩
  invFun v := ⟨e.weightEquiv.symm v.val, mem_foldedIndices.mpr <| by
    have hwsymm : (e.symm P P₂).weightEquiv.toLinearMap ∘ₗ τ.weightMap =
        σ.weightMap ∘ₗ (e.symm P P₂).weightEquiv.toLinearMap :=
      LinearMap.ext fun y ↦ e.weightEquiv.injective <| by
        simpa using (LinearMap.congr_fun hw (e.weightEquiv.symm y)).symm
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp v.property
    exact ⟨(e.symm P P₂).indexEquiv i, (weightMap_orbitSum (e.symm P P₂)
      ((e.symm P P₂).indexEquiv_apply_of_weightEquiv_comp_weightMap hwsymm) i).symm.trans
      (congrArg (e.symm P P₂).weightMap hi)⟩⟩
  left_inv u := Subtype.ext (e.weightEquiv.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.weightEquiv.apply_symm_apply v.val)

@[simp] private theorem coe_foldedIndicesCongr_apply (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (u : P.foldedIndices σ) : (foldedIndicesCongr e hw u : M₂) = e.weightMap (u : M) := by rfl
@[simp] private theorem coe_foldedIndicesCongr_symm_apply (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (v : P₂.foldedIndices τ) :
    ((foldedIndicesCongr e hw).symm v : M) = e.weightEquiv.symm (v : M₂) := by rfl

section MapEquiv

variable {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
  (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
  (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
  (hb : b.map e = b₂)

/-- **Transport an orbit-sum realization along an intertwining based equivalence.** -/
noncomputable def map : P₂.OrbitSumRealization b₂ τ :=
  let e_idx := foldedIndicesCongr e hw
  let f_fix := e.weightEquiv.fixedSubmoduleCongr hw
  let eqv := F.pairing.equivMapDual e_idx f_fix
  have hidx := e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw
  { pairing := F.pairing.mapDual e_idx f_fix, base := F.base.map eqv
    rootSystem := inferInstance, reduced := eqv.isReduced
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation x y := F.pairing.mapDual_toLinearMap_apply e_idx f_fix x y
    root_eq v := by
      rw [mapDual_root_apply, LinearEquiv.fixedSubmoduleCongr_apply, F.coe_root,
        coe_foldedIndicesCongr_symm_apply, e.weightEquiv.apply_symm_apply]
    base_eq v := by
      classical
      rw [F.base.support_map_eq, Finset.mem_image]
      refine ⟨fun ⟨u, hu, huv⟩ ↦ ?_, fun ⟨j₂, hj₂, hjv⟩ ↦ ?_⟩
      · obtain ⟨j, hj, hju⟩ := F.mem_support_base_iff.mp hu
        refine ⟨e.indexEquiv j, ?_, ?_⟩
        · rw [← hb, b.support_map_eq]; exact Finset.mem_image_of_mem _ hj
        · rw [← huv, equivMapDual_indexEquiv, coe_foldedIndicesCongr_apply, ← hju,
            weightMap_orbitSum e hidx j]
      · rw [← hb, b.support_map_eq, Finset.mem_image] at hj₂
        obtain ⟨j, hj, rfl⟩ := hj₂
        refine ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
          F.orbitSum_mem_support_base hj, Subtype.ext ?_⟩
        rw [equivMapDual_indexEquiv, coe_foldedIndicesCongr_apply, weightMap_orbitSum e hidx j,
          hjv] }

/-- The canonical based equivalence from `F.pairing` to `(F.map e hw hb).pairing`. -/
noncomputable def mapEquiv : F.pairing.Equiv (F.map e hw hb).pairing :=
  F.pairing.equivMapDual (foldedIndicesCongr e hw) (e.weightEquiv.fixedSubmoduleCongr hw)

@[simp] theorem coe_weightMap_mapEquiv (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.mapEquiv e hw hb).weightMap x : M₂) = e.weightMap (x : M) := by simp [mapEquiv, map]
@[simp] theorem coe_weightEquiv_mapEquiv_symm (y : LinearMap.fixedSubmodule τ.weightMap) :
    ((F.mapEquiv e hw hb).weightEquiv.symm y : M) = e.weightEquiv.symm (y : M₂) := by
  simp [mapEquiv, map]
@[simp] theorem coe_indexEquiv_mapEquiv (u : P.foldedIndices σ) :
    ((F.mapEquiv e hw hb).indexEquiv u : M₂) = e.weightMap (u : M) := by simp [mapEquiv, map]
@[simp] theorem indexEquiv_mapEquiv_orbitSum (i : ι) :
    (F.mapEquiv e hw hb).indexEquiv ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ =
      ⟨P₂.orbitSum τ (e.indexEquiv i), P₂.orbitSum_mem_foldedIndices τ (e.indexEquiv i)⟩ :=
  Subtype.ext <| (F.coe_indexEquiv_mapEquiv e hw hb _).trans
    (weightMap_orbitSum e (e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw) i)
@[simp] theorem coe_indexEquiv_mapEquiv_symm (v : P₂.foldedIndices τ) :
    ((F.mapEquiv e hw hb).indexEquiv.symm v : M) = e.weightEquiv.symm (v : M₂) := by
  simp [mapEquiv, map]
@[simp] theorem indexEquiv_mapEquiv_symm_orbitSum (j : ι₂) :
    (F.mapEquiv e hw hb).indexEquiv.symm ⟨P₂.orbitSum τ j, P₂.orbitSum_mem_foldedIndices τ j⟩ =
      ⟨P.orbitSum σ (e.indexEquiv.symm j),
        P.orbitSum_mem_foldedIndices σ (e.indexEquiv.symm j)⟩ :=
  (F.mapEquiv e hw hb).indexEquiv.injective <| by
    rw [_root_.Equiv.apply_symm_apply, indexEquiv_mapEquiv_orbitSum, _root_.Equiv.apply_symm_apply]
@[simp] theorem map_mapEquiv_base : F.base.map (F.mapEquiv e hw hb) = (F.map e hw hb).base := by rfl

end MapEquiv

section EquivOfMap

variable [IsDomain R] [CharZero R] {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
  (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ)

/-- Over a characteristic-zero domain, an intertwining based equivalence `e : P.Equiv P₂` induces a
canonical based equivalence between **any** two realizations `F₁` and `F₂`. -/
noncomputable def equivOfMap (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : F₁.pairing.Equiv F₂.pairing :=
  Subsingleton.elim (F₁.map e hw hb) F₂ ▸ F₁.mapEquiv e hw hb

variable (e : P.Equiv P₂)
  (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
  (hb : b.map e = b₂)

@[simp] theorem coe_weightMap_equivOfMap (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F₁.equivOfMap F₂ e hw hb).weightMap x : M₂) = e.weightMap (x : M) := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.coe_weightMap_mapEquiv e hw hb x
@[simp] theorem coe_weightEquiv_equivOfMap_symm (y : LinearMap.fixedSubmodule τ.weightMap) :
    ((F₁.equivOfMap F₂ e hw hb).weightEquiv.symm y : M) = e.weightEquiv.symm (y : M₂) := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.coe_weightEquiv_mapEquiv_symm e hw hb y
@[simp] theorem coe_indexEquiv_equivOfMap (u : P.foldedIndices σ) :
    ((F₁.equivOfMap F₂ e hw hb).indexEquiv u : M₂) = e.weightMap (u : M) := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.coe_indexEquiv_mapEquiv e hw hb u
@[simp] theorem indexEquiv_equivOfMap_orbitSum (i : ι) :
    (F₁.equivOfMap F₂ e hw hb).indexEquiv ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ =
      ⟨P₂.orbitSum τ (e.indexEquiv i), P₂.orbitSum_mem_foldedIndices τ (e.indexEquiv i)⟩ := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.indexEquiv_mapEquiv_orbitSum e hw hb i
@[simp] theorem coe_indexEquiv_equivOfMap_symm (v : P₂.foldedIndices τ) :
    ((F₁.equivOfMap F₂ e hw hb).indexEquiv.symm v : M) = e.weightEquiv.symm (v : M₂) := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.coe_indexEquiv_mapEquiv_symm e hw hb v
@[simp] theorem indexEquiv_equivOfMap_symm_orbitSum (j : ι₂) :
    (F₁.equivOfMap F₂ e hw hb).indexEquiv.symm
        ⟨P₂.orbitSum τ j, P₂.orbitSum_mem_foldedIndices τ j⟩ =
      ⟨P.orbitSum σ (e.indexEquiv.symm j),
        P.orbitSum_mem_foldedIndices σ (e.indexEquiv.symm j)⟩ := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); exact F₁.indexEquiv_mapEquiv_symm_orbitSum e hw hb j
@[simp] theorem map_equivOfMap_base : F₁.base.map (F₁.equivOfMap F₂ e hw hb) = F₂.base := by
  cases Subsingleton.elim F₂ (F₁.map e hw hb); rfl

end EquivOfMap
end Map
end OrbitSumRealization
end RootPairing
