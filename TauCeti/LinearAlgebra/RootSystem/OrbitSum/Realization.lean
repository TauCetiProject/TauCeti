/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.RootSystem.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.EquivComp
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.Map

/-!
# Orbit-sum realizations of a root-pairing automorphism

Let `P` be a root pairing, `b` a base of `P`, and `σ` an automorphism of `P`. When `σ` permutes the
simple roots of `b` and `P` is a root system, a vector of the weight space is fixed by `σ` if and
only if its coordinates in the simple-root basis `b.toWeightBasis` are constant along the
`σ`-orbits of `b.support`, yielding a basis `RootPairing.Base.fixedSubmoduleBasis` of
`LinearMap.fixedSubmodule σ.weightMap`. When `ι` is finite, its basis vectors are the distinct
simple-orbit sums `RootPairing.orbitSum P σ j` (`j ∈ b.support`), so the folded root vectors
`RootPairing.foldedRootEmb P σ` span `LinearMap.fixedSubmodule σ.weightMap` and the simple-orbit
sums are linearly independent and positively generate all positive orbit sums.

An **orbit-sum realization** (`RootPairing.OrbitSumRealization P b σ`) bundles a reduced
crystallographic root system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, indexed
by the distinct orbit sums `RootPairing.foldedIndices P σ`, paired by evaluation, whose roots are
the literal orbit-sum vectors and whose simple roots are the simple-orbit sums. Over a domain of
characteristic zero, the root vectors and evaluation pairing uniquely determine the coroots,
reflections, and base, so `P.OrbitSumRealization b σ` is a `Subsingleton`.

Whenever `σ` stabilizes `b` over a characteristic-zero ring, positivity in any
`OrbitSumRealization` matches positivity in `b`: the orbit sum of a root is positive for the folded
base if and only if the root is positive for `b`, so every positive folded root has a `b`-positive
lift. For `σ = 1` the realization recovers `(P, b)` including the empty root system on the zero
module (`RootPairing.OrbitSumRealization.one`), and any based equivalence intertwining two
automorphisms transports realizations and induces a canonical based equivalence on fixed submodules
(`RootPairing.OrbitSumRealization.map`, `RootPairing.OrbitSumRealization.equivOfMap`).

## Main definitions

* `RootPairing.Base.fixedSubmoduleBasis`: the basis of `LinearMap.fixedSubmodule σ.weightMap`
  indexed by the `σ`-cycles of `b.support`.
* `RootPairing.foldedRootEmb`: the canonical embedding of `P.foldedIndices σ` into
  `LinearMap.fixedSubmodule σ.weightMap`.
* `RootPairing.OrbitSumRealization`: bundled root system and base on the `σ`-fixed submodule whose
  roots are `P.foldedIndices σ` and whose simple roots are the simple-orbit sums.
* `RootPairing.OrbitSumRealization.one`: the canonical realization for `σ = 1`.
* `RootPairing.OrbitSumRealization.map`: transport of a realization along an intertwining based
  equivalence.

## Main results

* `RootPairing.Base.coe_fixedSubmoduleBasis_mk`: when `ι` is finite, the basis vector of
  `fixedSubmoduleBasis` at a simple root `j` is `P.orbitSum σ j`.
* `RootPairing.Base.span_foldedRootEmb_eq_top`, `RootPairing.Base.linearIndepOn_foldedRootEmb`, and
  `RootPairing.Base.foldedRootEmb_orbitSum_mem_closure_of_isPos`: spanning, simple-orbit linear
  independence, and positive-cone decomposition of `foldedRootEmb`.
* `RootPairing.OrbitSumRealization.ext` and `Subsingleton`: uniqueness of an orbit-sum realization
  over a characteristic-zero domain.
* `RootPairing.OrbitSumRealization.isPos_orbitSum_iff` and
  `RootPairing.OrbitSumRealization.isPos_iff_exists_isPos`: folded positive roots are precisely the
  orbit sums of `b`-positive roots.
* `RootPairing.OrbitSumRealization.equivOne`, `RootPairing.OrbitSumRealization.mapEquiv`, and
  `RootPairing.OrbitSumRealization.equivOfMap`: based equivalences for the identity fold and for
  intertwining root-pairing equivalences.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pp. 1–3.
-/

public section

namespace RootPairing

open Finset Function Set TauCeti

/-! ### Simple-orbit basis and folded root embedding -/

section FixedSubmoduleBasis

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The canonical embedding of the distinct orbit sums `P.foldedIndices σ` into
`LinearMap.fixedSubmodule σ.weightMap`. -/
def foldedRootEmb (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut) :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap where
  toFun u := ⟨(u : M), by
    obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
    exact hr ▸ P.orbitSum_mem_fixedSubmodule σ r⟩
  inj' := by
    intro _ _ h
    exact Subtype.ext (Subtype.mk.inj h)

@[simp]
theorem coe_foldedRootEmb_apply (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)
    (u : P.foldedIndices σ) :
    (P.foldedRootEmb σ u : M) = (u : M) := by
  rfl

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

/-- **The simple-orbit basis of the `σ`-fixed weight submodule.** Transporting the orbit-indicator
basis `Equiv.Perm.permutationFixedBasis` along the simple-root coordinate equivalence
`b.toWeightBasis.equivFun` yields a basis of `LinearMap.fixedSubmodule σ.weightMap` indexed by the
`σ`-cycles of `b.support`. -/
noncomputable def fixedSubmoduleBasis (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) R
      (LinearMap.fixedSubmodule σ.weightMap) :=
  let π := b.supportPerm hσ
  let qCongr : Quotient (Equiv.Perm.SameCycle.setoid π⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid π) :=
    Quotient.congr (_root_.Equiv.refl _) fun _ _ ↦ Equiv.Perm.sameCycle_inv
  ((Equiv.Perm.permutationFixedBasis (R := R) π⁻¹).reindex qCongr).map
    (b.toWeightBasis.equivFun.fixedSubmoduleCongr (b.equivFun_comp_weightMap hσ)).symm

/-- The coordinate of a `σ`-fixed vector on the simple orbit of `j` is its `b.toWeightBasis`
coordinate at `j`. -/
@[simp]
theorem fixedSubmoduleBasis_repr (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (x : LinearMap.fixedSubmodule σ.weightMap) (j : b.support) :
    (b.fixedSubmoduleBasis hσ).repr x (Quotient.mk _ j) = b.toWeightBasis.repr (x : M) j := by
  let π := b.supportPerm hσ
  let qCongr : Quotient (Equiv.Perm.SameCycle.setoid π⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid π) :=
    Quotient.congr (_root_.Equiv.refl b.support) fun _ _ ↦ Equiv.Perm.sameCycle_inv
  have hq : qCongr.symm (Quotient.mk _ j) = Quotient.mk _ j := rfl
  simp only [fixedSubmoduleBasis, Module.Basis.map_repr, LinearEquiv.trans_apply,
    Module.Basis.repr_reindex_apply]
  rw [hq, Equiv.Perm.permutationFixedBasis_repr]
  exact congrFun (LinearEquiv.fixedSubmoduleCongr_apply b.toWeightBasis.equivFun
    (b.equivFun_comp_weightMap hσ) x) j

/-- The coordinate of a `σ`-fixed vector on a simple cycle `O` is its `b.toWeightBasis` coordinate
at the chosen representative `O.out`. -/
theorem fixedSubmoduleBasis_repr_out (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (x : LinearMap.fixedSubmodule σ.weightMap)
    (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
    (b.fixedSubmoduleBasis hσ).repr x O = b.toWeightBasis.repr (x : M) O.out := by
  simpa only [Quotient.out_eq] using b.fixedSubmoduleBasis_repr hσ x O.out

section Finite

variable [Finite ι]

/-- Each basis vector of `fixedSubmoduleBasis` at a cycle `O` is the orbit sum of its representative
`O.out`. -/
theorem coe_fixedSubmoduleBasis_out (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
    ((b.fixedSubmoduleBasis hσ O) : M) = P.orbitSum σ (O.out : ι) := by
  classical
  apply b.toWeightBasis.equivFun.injective
  ext j
  rw [Module.Basis.equivFun_apply, ← b.fixedSubmoduleBasis_repr hσ (b.fixedSubmoduleBasis hσ O) j,
    Module.Basis.repr_self, Finsupp.single_apply, orbitSum_def, map_sum, Finset.sum_apply]
  have hmem : (j : ι) ∈ P.orbitIndices σ (O.out : ι) ↔
      Quotient.mk (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) j = O := by
    rw [mem_orbitIndices, ← b.sameCycle_supportPerm_iff hσ]
    exact ⟨fun h ↦ (Quotient.sound h.symm).trans (Quotient.out_eq O),
      fun h ↦ (Quotient.exact (h.trans (Quotient.out_eq O).symm)).symm⟩
  have hterm (k : ι) (hk : k ∈ P.orbitIndices σ (O.out : ι)) :
      b.toWeightBasis.equivFun (P.root k) j = if k = (j : ι) then 1 else 0 := by
    rw [Module.Basis.equivFun_apply]
    have hks : k ∈ b.support := b.orbitIndices_subset_support hσ O.out.2 hk
    have hbk : P.root k = b.toWeightBasis ⟨k, hks⟩ := (b.toWeightBasis_apply ⟨k, hks⟩).symm
    rw [hbk, Module.Basis.repr_self, Finsupp.single_apply]
    exact if_congr Subtype.ext_iff rfl rfl
  rw [Finset.sum_congr rfl fun k hk ↦ hterm k hk, Finset.sum_ite_eq']
  exact if_congr (eq_comm.trans hmem.symm) rfl rfl

/-- The basis vector of `fixedSubmoduleBasis` at the cycle of a simple root `j` is `P.orbitSum σ j`.
-/
@[simp]
theorem coe_fixedSubmoduleBasis_mk (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (j : b.support) :
    ((b.fixedSubmoduleBasis hσ (Quotient.mk _ j)) : M) = P.orbitSum σ j := by
  let O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) :=
    Quotient.mk (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) j
  rw [b.coe_fixedSubmoduleBasis_out hσ O]
  exact orbitSum_eq_of_mem (mem_orbitIndices.mpr
    ((b.sameCycle_supportPerm_iff hσ).mp (Quotient.exact (Quotient.out_eq O))).symm)

/-- When `σ` stabilizes `b.support`, the distinct root-orbit sums span
`LinearMap.fixedSubmodule σ.weightMap`. -/
theorem span_foldedRootEmb_eq_top (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    Submodule.span R (range (P.foldedRootEmb σ)) = ⊤ := by
  rw [eq_top_iff, ← (b.fixedSubmoduleBasis hσ).span_eq]
  refine Submodule.span_mono fun _ ⟨O, hO⟩ ↦ hO ▸ ?_
  exact ⟨⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩,
    Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm⟩

/-- When `σ` stabilizes `b.support`, the distinct simple-orbit sums are linearly independent in
`LinearMap.fixedSubmodule σ.weightMap`. -/
theorem linearIndepOn_foldedRootEmb (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    LinearIndepOn R (P.foldedRootEmb σ)
      {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [linearIndepOn_iff']
    intro _ _ _ _ _ _
    exact Subsingleton.elim _ _
  · let idxMap : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) → P.foldedIndices σ :=
      fun O ↦ ⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩
    have hcomp : P.foldedRootEmb σ ∘ idxMap = b.fixedSubmoduleBasis hσ :=
      funext fun O ↦ Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm
    have hli_comp : LinearIndependent R (P.foldedRootEmb σ ∘ idxMap) :=
      hcomp.symm ▸ (b.fixedSubmoduleBasis hσ).linearIndependent
    have hinj : Injective idxMap :=
      Function.Injective.of_comp (f := P.foldedRootEmb σ) hli_comp.injective
    have hrange : range idxMap =
        {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
      ext u
      refine ⟨fun ⟨O, hO⟩ ↦ hO ▸ ⟨O.out, O.out.2, rfl⟩, fun ⟨j, hj, hju⟩ ↦ ?_⟩
      let O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) := Quotient.mk _ ⟨j, hj⟩
      have hsc : Equiv.Perm.SameCycle σ.indexEquiv (O.out : ι) j :=
        (b.sameCycle_supportPerm_iff hσ).mp (Quotient.exact (Quotient.out_eq O))
      exact ⟨O, Subtype.ext ((orbitSum_eq_of_mem (mem_orbitIndices.mpr hsc.symm)).trans hju)⟩
    exact hrange ▸ (linearIndepOn_range_iff hinj _).mpr hli_comp

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
    have hbasis_sum : P.orbitSum σ r = ∑ j : b.support, c (j : ι) • b.toWeightBasis j := by
      rw [hc, ← Finset.sum_coe_sort b.support]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [b.toWeightBasis_apply]
    rw [hbasis_sum, map_sum, Finset.sum_apply, Finset.sum_eq_single O.out]
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
  exact ⟨⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩, ⟨O.out, O.out.2, rfl⟩,
    Subtype.ext (b.coe_fixedSubmoduleBasis_out hσ O).symm⟩

end Finite

end Base

end FixedSubmoduleBasis

/-! ### Bundled orbit-sum realizations -/

/-- An **orbit-sum realization** of `(P, b, σ)` bundles a reduced crystallographic root system on
the fixed submodule `LinearMap.fixedSubmodule σ.weightMap` and its `R`-linear dual, indexed by the
distinct root-orbit sums `P.foldedIndices σ`, paired by evaluation, whose roots are the literal
orbit-sum vectors and whose simple roots are the simple-orbit sums. -/
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
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (y : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x y = y x :=
  F.evaluation x y

@[simp]
theorem toLinearMap_eq_eval :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) := by
  ext x y
  exact F.evaluation x y

@[simp]
theorem coe_root (i : P.foldedIndices σ) : (F.pairing.root i : M) = (i : M) :=
  F.root_eq i

@[simp]
theorem root_orbitSum (j : ι) :
    F.pairing.root ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ =
      ⟨P.orbitSum σ j, P.orbitSum_mem_fixedSubmodule σ j⟩ :=
  Subtype.ext (F.coe_root _)

theorem coroot'_apply (i : P.foldedIndices σ) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' i x = F.pairing.coroot i x :=
  F.evaluation x (F.pairing.coroot i)

@[simp]
theorem mem_support_base_iff {i : P.foldedIndices σ} :
    i ∈ F.base.support ↔ ∃ j ∈ b.support, P.orbitSum σ j = (i : M) :=
  F.base_eq i

theorem orbitSum_mem_support_base {j : ι} (hj : j ∈ b.support) :
    ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ ∈ F.base.support :=
  F.mem_support_base_iff.mpr ⟨j, hj, rfl⟩

end Basic

/-! ### Uniqueness -/

section Uniqueness

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

/-- Any two orbit-sum realizations of `(P, b, σ)` over a characteristic-zero domain have the exact
same underlying root pairing. -/
theorem pairing_eq (F₁ F₂ : P.OrbitSumRealization b σ) : F₁.pairing = F₂.pairing := by
  apply IsRootSystem.ext
  · exact F₁.toLinearMap_eq_eval.trans F₂.toLinearMap_eq_eval.symm
  · ext i : 1
    exact Subtype.ext ((F₁.coe_root i).trans (F₂.coe_root i).symm)

/-- **Uniqueness of an orbit-sum realization.** Over a domain of characteristic zero, two
realizations have equal underlying root pairings and equal bases. -/
@[ext]
theorem ext (F₁ F₂ : P.OrbitSumRealization b σ) : F₁ = F₂ := by
  have hP := pairing_eq F₁ F₂
  cases F₁ with | mk p₁ b₁ rs₁ red₁ cry₁ ev₁ rt₁ bs₁ =>
  cases F₂ with | mk p₂ b₂ rs₂ red₂ cry₂ ev₂ rt₂ bs₂ =>
  subst hP
  congr
  exact Base.ext (Finset.ext fun i ↦ (bs₁ i).trans (bs₂ i).symm)

instance : Subsingleton (P.OrbitSumRealization b σ) := ⟨ext⟩

end Uniqueness

/-! ### Positive roots -/

section Positive

variable {ι R M N : Type*} [CommRing R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

/-- Over a characteristic-zero ring, when `σ` stabilizes `b.support`, every vector in the positive
root cone of `F` lies in the ambient positive root cone of `b`. -/
theorem coe_mem_posRootCone (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} (hx : x ∈ posRootCone F.pairing F.base) :
    (x : M) ∈ posRootCone P b := by
  obtain ⟨c, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
  rw [Submodule.coe_sum]
  refine sum_mem fun u hu ↦ ?_
  obtain ⟨j, hj, hju⟩ := F.mem_support_base_iff.mp hu
  rw [Submodule.coe_smul_of_tower, F.coe_root, ← hju]
  exact nsmul_mem (orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hj)) (c u)

/-- **Positivity of an orbit sum in `F.base` matches positivity in `b`** when `σ` stabilizes
`b.support` over a characteristic-zero ring. -/
theorem isPos_orbitSum_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (j : ι) :
    F.base.IsPos ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ ↔ b.IsPos j := by
  have hpos {k : ι} (hk : b.IsPos k) :
      F.base.IsPos ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := by
    set u : P.foldedIndices σ := ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩
    by_contra hnot
    have hneg_pos : F.pairing.reflectionPerm u u ∈ posRoots F.pairing F.base :=
      (mem_posRoots _ _ _).mpr
        ((isPos_reflectionPerm_self_iff_mem_negRoots F.pairing F.base u).mpr
          ((mem_negRoots _ _ _).mpr hnot))
    have hneg : -P.orbitSum σ k ∈ posRootCone P b := by
      have hm := F.coe_mem_posRootCone hσ
        (root_mem_posRootCone_of_mem_posRoots F.pairing F.base hneg_pos)
      rwa [root_reflectionPerm, reflection_apply_self, Submodule.coe_neg, F.coe_root] at hm
    exact orbitSum_ne_zero hσ k (eq_zero_of_add_eq_zero_of_mem_posRootCone P b
      (orbitSum_mem_posRootCone hσ hk) hneg (add_neg_cancel _))
  refine ⟨fun h ↦ ?_, hpos⟩
  by_contra hnot
  have hneg_pos : b.IsPos (P.reflectionPerm j j) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr ((mem_negRoots P b j).mpr hnot)
  have h₁ : P.orbitSum σ j ∈ posRootCone P b := by
    simpa [F.coe_root] using F.coe_mem_posRootCone hσ
      (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr h))
  have h₂ : -P.orbitSum σ j ∈ posRootCone P b := by
    simpa [orbitSum_reflectionPerm_self] using orbitSum_mem_posRootCone hσ hneg_pos
  exact orbitSum_ne_zero hσ j (eq_zero_of_add_eq_zero_of_mem_posRootCone P b h₁ h₂
    (add_neg_cancel _))

/-- **Over a characteristic-zero ring, when `σ` stabilizes `b.support`, a folded root is
`F.base`-positive if and only if it is the orbit sum of a `b`-positive root.** -/
theorem isPos_iff_exists_isPos (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    (u : P.foldedIndices σ) :
    F.base.IsPos u ↔ ∃ j, b.IsPos j ∧ P.orbitSum σ j = (u : M) := by
  obtain ⟨j, hj⟩ := mem_foldedIndices.mp u.2
  have hu : u = ⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ := Subtype.ext hj.symm
  refine ⟨fun h ↦ ⟨j, (F.isPos_orbitSum_iff hσ j).mp (hu ▸ h), hj⟩, ?_⟩
  rintro ⟨k, hk, hku⟩
  have huk : u = ⟨P.orbitSum σ k, P.orbitSum_mem_foldedIndices σ k⟩ := Subtype.ext hku.symm
  exact huk ▸ (F.isPos_orbitSum_iff hσ k).mpr hk

end Positive

/-! ### Identity realization -/

section One

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι]

private noncomputable def foldedIndicesOneEquiv : ι ≃ P.foldedIndices 1 :=
  _root_.Equiv.ofBijective (fun i ↦ ⟨P.root i, P.foldedIndices_one ▸ Set.mem_range_self i⟩)
    ⟨fun _ _ h ↦ P.root.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ ↦ by
      obtain ⟨i, rfl⟩ := P.foldedIndices_one ▸ hx
      exact ⟨i, rfl⟩⟩

@[simp]
private theorem coe_foldedIndicesOneEquiv_apply (i : ι) :
    (foldedIndicesOneEquiv P i : M) = P.root i :=
  rfl

variable [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base)

/-- **The identity automorphism realizes the original based root system** on the fixed submodule
`LinearMap.fixedSubmodule (1 : P.Aut).weightMap` (which is all of `M`), including the empty root
system on the zero module. -/
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
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.2
      have heu : e i = u := Subtype.ext ((coe_foldedIndicesOneEquiv_apply P i).trans
        ((orbitSum_one P i).symm.trans hi))
      rw [← heu, mapDual_root_apply, _root_.Equiv.symm_apply_apply]
      exact (coe_foldedIndicesOneEquiv_apply P i).symm
    base_eq u := by
      classical
      rw [b.support_map_eq, Finset.mem_image]
      refine ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, ?_⟩, fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, ?_⟩⟩
      · rw [← hju, equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply, orbitSum_one]
      · refine Subtype.ext ?_
        rw [equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply, ← hju, orbitSum_one] }

/-- The canonical equivalence of root pairings from `P` to `(OrbitSumRealization.one P b).pairing`.
-/
noncomputable def equivOne : P.Equiv (one P b).pairing :=
  P.equivMapDual (foldedIndicesOneEquiv P)
    (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm

-- `@[simp]` is placed on `weightMap_equivOne`, `weightEquiv_equivOne`, `indexEquiv_equivOne`, and
-- `indexEquiv_equivOne_symm_root` because `Hom.weightMap_one` and `orbitSum_one` rewrite the
-- implicit `DFunLike.coe` / `LinearEquiv.symm` types on `coe_weightMap_equivOne` (`simpNF`).
@[simp]
theorem weightMap_equivOne :
    (equivOne P b).weightMap =
      (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
        (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm.toLinearMap := by
  dsimp only [equivOne, one]
  rw [equivMapDual_weightMap]

theorem coe_weightMap_equivOne (x : M) : ((equivOne P b).weightMap x : M) = x := by
  rw [weightMap_equivOne]
  rfl

@[simp]
theorem weightEquiv_equivOne :
    (equivOne P b).weightEquiv =
      (LinearEquiv.ofTop (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
        (LinearMap.fixedSubmodule_eq_top_iff.mpr rfl)).symm := by
  dsimp only [equivOne, one]
  rw [equivMapDual_weightEquiv]

theorem weightEquiv_equivOne_symm_apply (x : LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :
    (equivOne P b).weightEquiv.symm x = (x : M) := by
  rw [weightEquiv_equivOne]
  rfl

@[simp]
theorem indexEquiv_equivOne (i : ι) :
    (equivOne P b).indexEquiv i = ⟨P.root i, P.foldedIndices_one ▸ Set.mem_range_self i⟩ := by
  apply Subtype.ext
  dsimp only [equivOne, one]
  rw [equivMapDual_indexEquiv, coe_foldedIndicesOneEquiv_apply]

theorem coe_indexEquiv_equivOne (i : ι) :
    ((equivOne P b).indexEquiv i : M) = P.root i := by
  simp

theorem indexEquiv_equivOne_orbitSum_eq (i : ι) :
    (equivOne P b).indexEquiv i = ⟨P.orbitSum 1 i, P.orbitSum_mem_foldedIndices 1 i⟩ := by
  simp

@[simp]
theorem indexEquiv_equivOne_symm_root (i : ι) (h : P.root i ∈ P.foldedIndices 1) :
    (equivOne P b).indexEquiv.symm ⟨P.root i, h⟩ = i := by
  apply (equivOne P b).indexEquiv.injective
  rw [_root_.Equiv.apply_symm_apply, indexEquiv_equivOne]

theorem indexEquiv_equivOne_symm_orbitSum (i : ι) :
    (equivOne P b).indexEquiv.symm ⟨P.orbitSum 1 i, P.orbitSum_mem_foldedIndices 1 i⟩ = i := by
  simp

@[simp]
theorem map_equivOne_base : b.map (equivOne P b) = (one P b).base := by
  rfl

end One

/-! ### Transport along intertwining equivalences -/

section Map

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
  [Finite ι] [Finite ι₂]

private noncomputable def foldedIndicesCongr (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ where
  toFun u := ⟨e.weightEquiv u.val, mem_foldedIndices.mpr <| by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.2
    exact ⟨e.indexEquiv i, (weightMap_orbitSum e
      (e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw) i).symm.trans
      (congrArg e.weightMap hi)⟩⟩
  invFun v := ⟨e.weightEquiv.symm v.val, mem_foldedIndices.mpr <| by
    have hwsymm : (e.symm P P₂).weightEquiv.toLinearMap ∘ₗ τ.weightMap =
        σ.weightMap ∘ₗ (e.symm P P₂).weightEquiv.toLinearMap := by
      ext y
      apply e.weightEquiv.injective
      have := LinearMap.congr_fun hw (e.weightEquiv.symm y)
      simpa using this.symm
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp v.2
    exact ⟨(e.symm P P₂).indexEquiv i, (weightMap_orbitSum (e.symm P P₂)
      ((e.symm P P₂).indexEquiv_apply_of_weightEquiv_comp_weightMap hwsymm) i).symm.trans
      (congrArg (e.symm P P₂).weightMap hi)⟩⟩
  left_inv u := Subtype.ext (e.weightEquiv.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.weightEquiv.apply_symm_apply v.val)

@[simp]
private theorem coe_foldedIndicesCongr_apply (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (u : P.foldedIndices σ) :
    (foldedIndicesCongr e hw u : M₂) = e.weightMap (u : M) :=
  rfl

@[simp]
private theorem coe_foldedIndicesCongr_symm_apply (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (v : P₂.foldedIndices τ) :
    ((foldedIndicesCongr e hw).symm v : M) = e.weightEquiv.symm (v : M₂) :=
  rfl

/-- **Transport an orbit-sum realization along an intertwining based equivalence.** -/
noncomputable def map {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : P₂.OrbitSumRealization b₂ τ :=
  let e_idx := foldedIndicesCongr e hw
  let f_fix := e.weightEquiv.fixedSubmoduleCongr hw
  let eqv := F.pairing.equivMapDual e_idx f_fix
  have hidx := e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw
  { pairing := F.pairing.mapDual e_idx f_fix
    base := F.base.map eqv
    rootSystem := inferInstance
    reduced := eqv.isReduced
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation x y := F.pairing.mapDual_toLinearMap_apply e_idx f_fix x y
    root_eq v := by
      rw [mapDual_root_apply, LinearEquiv.fixedSubmoduleCongr_apply, F.coe_root,
        coe_foldedIndicesCongr_symm_apply, e.weightEquiv.apply_symm_apply]
    base_eq v := by
      classical
      rw [F.base.support_map_eq, Finset.mem_image]
      refine ⟨?_, ?_⟩
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨j, hj, hju⟩ := F.mem_support_base_iff.mp hu
        refine ⟨e.indexEquiv j, ?_, ?_⟩
        · rw [← hb, b.support_map_eq]
          exact Finset.mem_image_of_mem _ hj
        · rw [equivMapDual_indexEquiv, coe_foldedIndicesCongr_apply, ← hju,
            weightMap_orbitSum e hidx j]
      · rintro ⟨j₂, hj₂, hjv⟩
        rw [← hb, b.support_map_eq, Finset.mem_image] at hj₂
        obtain ⟨j, hj, rfl⟩ := hj₂
        refine ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
          F.orbitSum_mem_support_base hj, Subtype.ext ?_⟩
        rw [equivMapDual_indexEquiv, coe_foldedIndicesCongr_apply, weightMap_orbitSum e hidx j,
          hjv] }

/-- The canonical based equivalence from `F.pairing` to `(F.map e hw hb).pairing`. -/
noncomputable def mapEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : F.pairing.Equiv (F.map e hw hb).pairing :=
  F.pairing.equivMapDual (foldedIndicesCongr e hw) (e.weightEquiv.fixedSubmoduleCongr hw)

@[simp]
theorem coe_weightMap_mapEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.mapEquiv e hw hb).weightMap x : M₂) = e.weightMap (x : M) := by
  simp [mapEquiv, map]

@[simp]
theorem coe_weightEquiv_mapEquiv_symm {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (y : LinearMap.fixedSubmodule τ.weightMap) :
    ((F.mapEquiv e hw hb).weightEquiv.symm y : M) = e.weightEquiv.symm (y : M₂) := by
  simp [mapEquiv, map]

@[simp]
theorem coe_indexEquiv_mapEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (u : P.foldedIndices σ) :
    ((F.mapEquiv e hw hb).indexEquiv u : M₂) = e.weightMap (u : M) := by
  simp [mapEquiv, map]

@[simp]
theorem indexEquiv_mapEquiv_orbitSum {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (i : ι) :
    (F.mapEquiv e hw hb).indexEquiv ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ =
      ⟨P₂.orbitSum τ (e.indexEquiv i), P₂.orbitSum_mem_foldedIndices τ (e.indexEquiv i)⟩ :=
  Subtype.ext <| (F.coe_indexEquiv_mapEquiv e hw hb _).trans
    (weightMap_orbitSum e (e.indexEquiv_apply_of_weightEquiv_comp_weightMap hw) i)

@[simp]
theorem coe_indexEquiv_mapEquiv_symm {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (v : P₂.foldedIndices τ) :
    ((F.mapEquiv e hw hb).indexEquiv.symm v : M) = e.weightEquiv.symm (v : M₂) := by
  simp [mapEquiv, map]

@[simp]
theorem indexEquiv_mapEquiv_symm_orbitSum {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (j : ι₂) :
    (F.mapEquiv e hw hb).indexEquiv.symm ⟨P₂.orbitSum τ j, P₂.orbitSum_mem_foldedIndices τ j⟩ =
      ⟨P.orbitSum σ (e.indexEquiv.symm j),
        P.orbitSum_mem_foldedIndices σ (e.indexEquiv.symm j)⟩ := by
  apply (F.mapEquiv e hw hb).indexEquiv.injective
  rw [_root_.Equiv.apply_symm_apply, indexEquiv_mapEquiv_orbitSum, _root_.Equiv.apply_symm_apply]

@[simp]
theorem map_mapEquiv_base {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : F.base.map (F.mapEquiv e hw hb) = (F.map e hw hb).base := by
  rfl

/-- Over a characteristic-zero domain, an intertwining based equivalence `e : P.Equiv P₂` induces a
canonical based equivalence between **any** two realizations `F₁` and `F₂`, acting on fixed vectors
by `e.weightMap`. -/
noncomputable def equivOfMap [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : F₁.pairing.Equiv F₂.pairing :=
  Subsingleton.elim (F₁.map e hw hb) F₂ ▸ F₁.mapEquiv e hw hb

@[simp]
theorem coe_weightMap_equivOfMap [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F₁.equivOfMap F₂ e hw hb).weightMap x : M₂) = e.weightMap (x : M) := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.coe_weightMap_mapEquiv e hw hb x

@[simp]
theorem coe_weightEquiv_equivOfMap_symm [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (y : LinearMap.fixedSubmodule τ.weightMap) :
    ((F₁.equivOfMap F₂ e hw hb).weightEquiv.symm y : M) = e.weightEquiv.symm (y : M₂) := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.coe_weightEquiv_mapEquiv_symm e hw hb y

@[simp]
theorem coe_indexEquiv_equivOfMap [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (u : P.foldedIndices σ) :
    ((F₁.equivOfMap F₂ e hw hb).indexEquiv u : M₂) = e.weightMap (u : M) := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.coe_indexEquiv_mapEquiv e hw hb u

@[simp]
theorem indexEquiv_equivOfMap_orbitSum [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (i : ι) :
    (F₁.equivOfMap F₂ e hw hb).indexEquiv ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ =
      ⟨P₂.orbitSum τ (e.indexEquiv i), P₂.orbitSum_mem_foldedIndices τ (e.indexEquiv i)⟩ := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.indexEquiv_mapEquiv_orbitSum e hw hb i

@[simp]
theorem coe_indexEquiv_equivOfMap_symm [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (v : P₂.foldedIndices τ) :
    ((F₁.equivOfMap F₂ e hw hb).indexEquiv.symm v : M) = e.weightEquiv.symm (v : M₂) := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.coe_indexEquiv_mapEquiv_symm e hw hb v

@[simp]
theorem indexEquiv_equivOfMap_symm_orbitSum [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) (j : ι₂) :
    (F₁.equivOfMap F₂ e hw hb).indexEquiv.symm
        ⟨P₂.orbitSum τ j, P₂.orbitSum_mem_foldedIndices τ j⟩ =
      ⟨P.orbitSum σ (e.indexEquiv.symm j),
        P.orbitSum_mem_foldedIndices σ (e.indexEquiv.symm j)⟩ := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  exact F₁.indexEquiv_mapEquiv_symm_orbitSum e hw hb j

@[simp]
theorem map_equivOfMap_base [IsDomain R] [CharZero R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : F₁.base.map (F₁.equivOfMap F₂ e hw hb) = F₂.base := by
  obtain rfl : F₂ = F₁.map e hw hb := Subsingleton.elim _ _
  rfl

end Map

end OrbitSumRealization

end RootPairing
