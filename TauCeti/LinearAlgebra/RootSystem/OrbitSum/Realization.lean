/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.RootSystem.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Orbit-sum realizations of a root-pairing automorphism

Let `P` be a root pairing with finitely many roots, `b` a base of `P`, and `σ` an automorphism of
`P`. When `σ` permutes the simple roots of `b` and `P` is a root system, a vector of the weight
space is fixed by `σ` if and only if its coordinates in the simple-root basis `b.toWeightBasis` are
constant along the `σ`-orbits of `b.support`. Consequently the simple-orbit sums
`RootPairing.orbitSum P σ i` (`i ∈ b.support`) form a basis `RootPairing.Base.fixedSubmoduleBasis`
of `LinearMap.fixedSubmodule σ.weightMap`.

An **orbit-sum realization** (`RootPairing.OrbitSumRealization P b σ`) bundles a reduced
crystallographic root system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, indexed
by the distinct orbit sums `RootPairing.foldedIndices P σ`, paired by evaluation, whose roots are
the literal orbit-sum vectors and whose simple roots are the simple-orbit sums. Over a domain of
characteristic zero, the root vectors and evaluation pairing uniquely determine the coroots,
reflections, and base, so `P.OrbitSumRealization b σ` is a `Subsingleton`.

Whenever `σ` stabilizes `b`, positivity in any `OrbitSumRealization` matches positivity in `b`: the
orbit sum of a root is positive for the folded base if and only if the root is positive for `b`, so
every positive folded root has a `b`-positive lift. For `σ = 1` the realization recovers `(P, b)`
including the empty root system on the zero module (`RootPairing.OrbitSumRealization.one`), and any
based equivalence intertwining two automorphisms transports realizations and induces a canonical
based equivalence on fixed submodules (`RootPairing.OrbitSumRealization.map`,
`RootPairing.OrbitSumRealization.equivOfMap`).

## Main definitions

* `RootPairing.Base.supportPerm`: the permutation of `b.support` induced by a base-preserving
  automorphism `σ`.
* `RootPairing.Base.fixedSubmoduleBasis`: the basis of `LinearMap.fixedSubmodule σ.weightMap` formed
  by the distinct simple-orbit sums.
* `RootPairing.OrbitSumRealization`: bundled root system and base on the `σ`-fixed submodule whose
  roots are `P.foldedIndices σ` and whose simple roots are the simple-orbit sums.
* `RootPairing.OrbitSumRealization.one`: the canonical realization for `σ = 1`.
* `RootPairing.OrbitSumRealization.map`: transport of a realization along an intertwining based
  equivalence.

## Main results

* `RootPairing.Base.orbitSum_eq_orbitSum_iff_of_mem_support`: over a nontrivial ring, two simple
  roots have the same orbit sum if and only if they lie in the same `σ`-orbit.
* `RootPairing.OrbitSumRealization.ext` and `Subsingleton`: uniqueness of an orbit-sum realization
  over a characteristic-zero domain.
* `RootPairing.OrbitSumRealization.isPos_orbitSum_iff` and
  `RootPairing.OrbitSumRealization.isPos_iff_exists_isPos`: folded positive roots are precisely the
  orbit sums of `b`-positive roots.
* `RootPairing.OrbitSumRealization.equivOne` and `RootPairing.OrbitSumRealization.equivOfMap`:
  based equivalences for the identity fold and for intertwining root-pairing equivalences.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pp. 1–3.
-/

public section

namespace RootPairing

open Finset Function Set TauCeti

/-! ### Simple-orbit basis of the fixed submodule -/

namespace Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} {σ : P.Aut}

section Any

variable (b : P.Base)

/-- An automorphism mapping `b.support` into itself permutes `b.support`: an index belongs to
`b.support` if and only if its image does. -/
theorem indexEquiv_mem_support_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i : ι} :
    σ.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  classical
  refine ⟨fun hi ↦ ?_, hσ i⟩
  have hmap : σ.indexEquiv i ∈ (b.map σ).support := by
    rwa [b.map_eq_of_forall_mem_support hσ]
  rw [b.support_map_eq, Finset.mem_image] at hmap
  obtain ⟨j, hj, hji⟩ := hmap
  exact σ.indexEquiv.injective hji ▸ hj

/-- The permutation of `b.support` induced by an automorphism stabilizing `b.support`. -/
noncomputable def supportPerm (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Equiv.Perm b.support :=
  Equiv.Perm.subtypePerm σ.indexEquiv fun _ ↦ b.indexEquiv_mem_support_iff hσ

@[simp]
theorem coe_supportPerm_apply (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : b.support) :
    (b.supportPerm hσ i : ι) = σ.indexEquiv i := by
  simp [supportPerm]

theorem sameCycle_supportPerm_iff (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {i j : b.support} :
    Equiv.Perm.SameCycle (b.supportPerm hσ) i j ↔
      Equiv.Perm.SameCycle σ.indexEquiv (i : ι) (j : ι) := by
  refine exists_congr fun k ↦ ?_
  rw [← Subtype.coe_inj, supportPerm, Equiv.Perm.subtypePerm_zpow, Equiv.Perm.subtypePerm_apply]

end Any

section Finite

variable [Finite ι]

/-- If `i ∈ b.support` and `σ` stabilizes `b.support`, every member of the root orbit of `i` lies in
`b.support`. -/
theorem orbitIndices_subset_support (b : P.Base)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {i : ι} (hi : i ∈ b.support) : P.orbitIndices σ i ⊆ b.support := by
  intro j hj
  rcases (mem_orbitIndices_iff_exists_pow (P := P)).mp hj with ⟨k, rfl⟩
  clear hj
  induction k with
  | zero => exact hi
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hσ _ ih

/-- Over a nontrivial ring, two simple roots of `b` have the same orbit sum under a base-preserving
automorphism if and only if they belong to the same `σ`-orbit. -/
theorem orbitSum_eq_orbitSum_iff_of_mem_support [Nontrivial R] (b : P.Base)
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.orbitSum σ i = P.orbitSum σ j ↔ j ∈ P.orbitIndices σ i := by
  refine ⟨fun heq ↦ ?_, fun hmem ↦ (orbitSum_eq_of_mem hmem).symm⟩
  classical
  have hsub_i := b.orbitIndices_subset_support hσ hi
  have hsub_j := b.orbitIndices_subset_support hσ hj
  have hsum (s : Finset ι) (hs : s ⊆ b.support) :
      ∑ k ∈ s, P.root k = ∑ k ∈ b.support, (if k ∈ s then (1 : R) else 0) • P.root k := by
    simp_rw [ite_smul, one_smul, zero_smul, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hs]
  rw [orbitSum_def, orbitSum_def, hsum _ hsub_i, hsum _ hsub_j, ← sub_eq_zero,
    ← Finset.sum_sub_distrib] at heq
  simp_rw [← sub_smul] at heq
  have hcoeff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support
    (fun k ↦ (if k ∈ P.orbitIndices σ i then (1 : R) else 0) -
      if k ∈ P.orbitIndices σ j then 1 else 0) (fun _ h ↦ h) heq j hj
  simp only [self_mem_orbitIndices, ite_true, sub_eq_zero] at hcoeff
  by_contra hnot
  simp [hnot] at hcoeff

section Basis

variable [P.IsRootSystem] (b : P.Base)

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

/-- **The simple-orbit sums form a basis of the `σ`-fixed weight submodule.** Transporting the
orbit-indicator basis `Equiv.Perm.permutationFixedBasis` along the simple-root coordinate
equivalence `b.toWeightBasis.equivFun` yields a basis of `LinearMap.fixedSubmodule σ.weightMap`
indexed by the `σ`-cycles of `b.support`. -/
noncomputable def fixedSubmoduleBasis (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    Module.Basis (Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) R
      (LinearMap.fixedSubmodule σ.weightMap) :=
  let π := b.supportPerm hσ
  let qCongr : Quotient (Equiv.Perm.SameCycle.setoid π⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid π) :=
    Quotient.congr (_root_.Equiv.refl _) fun _ _ ↦ Equiv.Perm.sameCycle_inv
  ((Equiv.Perm.permutationFixedBasis (R := R) π⁻¹).reindex qCongr).map
    (b.toWeightBasis.equivFun.fixedSubmoduleCongr (b.equivFun_comp_weightMap hσ)).symm

/-- The coordinate of a `σ`-fixed vector on a simple orbit is its `b.toWeightBasis` coordinate at
any simple root in that orbit. -/
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

/-- Each basis vector of `fixedSubmoduleBasis` is the orbit sum of the simple roots in that
cycle. -/
@[simp]
theorem coe_fixedSubmoduleBasis (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
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

end Basis

end Finite

end Base

/-! ### Auxiliary dual transport for root pairings -/

section MapDual

variable {ι ι₂ R M N M₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂]

/-- Transport a root pairing along an index bijection `e : ι ≃ ι₂` and weight-space equivalence
`f : M ≃ₗ[R] M₂` onto `M₂` paired with its linear dual `Module.Dual R M₂` by evaluation. -/
private noncomputable def mapDual (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) :
    RootPairing ι₂ R M₂ (Module.Dual R M₂) :=
  P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)

private instance (P : RootPairing ι R M N) [P.IsRootSystem] (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) :
    (P.mapDual e f).IsRootSystem :=
  inferInstanceAs (P.map e f (P.flip.toPerfPair.trans f.symm.dualMap)).IsRootSystem

private theorem mapDual_toLinearMap_apply (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂)
    (x : M₂) (φ : Module.Dual R M₂) :
    (P.mapDual e f).toLinearMap x φ = φ x := by
  change ((f.symm.trans P.toPerfPair).trans
    (P.flip.toPerfPair.trans f.symm.dualMap).symm.dualMap) x φ = φ x
  simp

private theorem mapDual_root_apply (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂)
    (i : ι₂) :
    (P.mapDual e f).root i = f (P.root (e.symm i)) :=
  rfl

/-- The canonical equivalence of root pairings from `P` to `P.mapDual e f`. -/
private noncomputable def equivMapDual (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) :
    P.Equiv (P.mapDual e f) where
  weightMap := f.toLinearMap
  coweightMap := (P.flip.toPerfPair.trans f.symm.dualMap).symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by
    ext φ x
    simp [mapDual_toLinearMap_apply]
  root_weightMap := by
    ext i
    simp [mapDual_root_apply]
  coroot_coweightMap := by
    ext i
    exact (P.flip.toPerfPair.trans f.symm.dualMap).symm_apply_apply (P.coroot (e.symm i))
  bijective_weightMap := f.bijective
  bijective_coweightMap := (P.flip.toPerfPair.trans f.symm.dualMap).symm.bijective

private theorem isReduced_of_equiv {N₂ : Type*} [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂} [P.IsReduced] (g : P.Equiv Q) :
    Q.IsReduced := by
  rw [isReduced_iff']
  intro i₂ j₂ hij hdep
  obtain ⟨i, rfl⟩ := g.indexEquiv.surjective i₂
  obtain ⟨j, rfl⟩ := g.indexEquiv.surjective j₂
  have hdep' : ¬ LinearIndependent R ![P.root i, P.root j] :=
    mt (g.toHom.linearIndependent_root_indexEquiv_iff g.bijective_weightMap.injective i j).mpr hdep
  rcases IsReduced.eq_or_eq_neg i j hdep' with hroot | hroot
  · exact absurd (congrArg g.indexEquiv (P.root.injective hroot)) hij
  · calc Q.root (g.indexEquiv i)
      _ = g.weightMap (P.root i) := (Hom.root_weightMap_apply P Q i g.toHom).symm
      _ = g.weightMap (-P.root j) := by rw [hroot]
      _ = -Q.root (g.indexEquiv j) := by rw [map_neg, Hom.root_weightMap_apply P Q j g.toHom]

end MapDual

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

/-- Every vector in the positive root cone of `F` lies in the ambient positive root cone of `b`. -/
theorem coe_mem_posRootCone (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} (hx : x ∈ posRootCone F.pairing F.base) :
    (x : M) ∈ posRootCone P b := by
  obtain ⟨c, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
  rw [Submodule.coe_sum]
  refine sum_mem fun u hu ↦ ?_
  obtain ⟨j, hj, hju⟩ := F.mem_support_base_iff.mp hu
  rw [Submodule.coe_smul_of_tower, F.coe_root, ← hju]
  exact nsmul_mem (orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hj)) (c u)

/-- **Positivity of an orbit sum in `F.base` matches positivity in `b`.** -/
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

/-- **A folded root is `F.base`-positive if and only if it is the orbit sum of a `b`-positive
root.** -/
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

private theorem coe_foldedIndicesOneEquiv_apply (i : ι) :
    (foldedIndicesOneEquiv P i : M) = P.root i :=
  rfl

private def fixedSubmoduleOneEquiv : M ≃ₗ[R] LinearMap.fixedSubmodule (1 : P.Aut).weightMap where
  toFun x := ⟨x, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base)

/-- **The identity automorphism realizes the original based root system** on the fixed submodule
`LinearMap.fixedSubmodule (1 : P.Aut).weightMap` (which is all of `M`), including the empty root
system on the zero module. -/
noncomputable def one : P.OrbitSumRealization b 1 :=
  let e := foldedIndicesOneEquiv P
  let f := fixedSubmoduleOneEquiv (R := R) P
  let eqv := P.equivMapDual e f
  { pairing := P.mapDual e f
    base := b.map eqv
    rootSystem := inferInstance
    reduced := isReduced_of_equiv eqv
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation x y := mapDual_toLinearMap_apply P e f x y
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
      · rw [← hju, orbitSum_one]
        exact (coe_foldedIndicesOneEquiv_apply P j).symm
      · refine Subtype.ext ?_
        rw [← hju, orbitSum_one]
        exact coe_foldedIndicesOneEquiv_apply P j }

/-- The canonical equivalence of root pairings from `P` to `(OrbitSumRealization.one P b).pairing`.
-/
noncomputable def equivOne : P.Equiv (one P b).pairing :=
  P.equivMapDual (foldedIndicesOneEquiv P) (fixedSubmoduleOneEquiv P)

theorem coe_weightMap_equivOne (x : M) : ((equivOne P b).weightMap x : M) = x := by
  rfl

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

/-- When the roots of `P` span, an equivalence intertwining `σ` and `τ` on root indices intertwines
their weight-space endomorphisms on all of `M`. -/
theorem _root_.RootPairing.Equiv.weightMap_comp_eq_of_indexEquiv [P.IsRootSystem]
    (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j)) :
    e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap := by
  apply LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P))
  intro j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.weightEquiv_apply,
    Hom.root_weightMap_apply P P j σ.toHom, Hom.root_weightMap_apply P P₂ _ e.toHom,
    Hom.root_weightMap_apply P₂ P₂ _ τ.toHom, h j]

private theorem indexEquiv_intertwine_of_weightMap (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (j : ι) :
    e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j) := by
  apply P₂.root.injective
  have hx := LinearMap.congr_fun hw (P.root j)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Equiv.weightEquiv_apply,
    Hom.root_weightMap_apply P P j σ.toHom, Hom.root_weightMap_apply P P₂ _ e.toHom,
    Hom.root_weightMap_apply P₂ P₂ _ τ.toHom] using hx

variable [Finite ι] [Finite ι₂]

private noncomputable def foldedIndicesCongr (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ where
  toFun u := ⟨e.weightEquiv u.val, mem_foldedIndices.mpr <| by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp u.2
    exact ⟨e.indexEquiv i, (weightMap_orbitSum e
      (indexEquiv_intertwine_of_weightMap e hw) i).symm.trans (congrArg e.weightMap hi)⟩⟩
  invFun v := ⟨e.weightEquiv.symm v.val, mem_foldedIndices.mpr <| by
    have hwsymm : (e.symm P P₂).weightEquiv.toLinearMap ∘ₗ τ.weightMap =
        σ.weightMap ∘ₗ (e.symm P P₂).weightEquiv.toLinearMap := by
      ext y
      apply e.weightEquiv.injective
      have := LinearMap.congr_fun hw (e.weightEquiv.symm y)
      simpa using this.symm
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp v.2
    exact ⟨(e.symm P P₂).indexEquiv i, (weightMap_orbitSum (e.symm P P₂)
      (indexEquiv_intertwine_of_weightMap (e.symm P P₂) hwsymm) i).symm.trans
      (congrArg (e.symm P P₂).weightMap hi)⟩⟩
  left_inv u := Subtype.ext (e.weightEquiv.symm_apply_apply u.val)
  right_inv v := Subtype.ext (e.weightEquiv.apply_symm_apply v.val)

/-- **Transport an orbit-sum realization along an intertwining based equivalence.** -/
noncomputable def map {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hw : e.weightEquiv.toLinearMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightEquiv.toLinearMap)
    (hb : b.map e = b₂) : P₂.OrbitSumRealization b₂ τ :=
  let e_idx := foldedIndicesCongr e hw
  let f_fix := e.weightEquiv.fixedSubmoduleCongr hw
  let eqv := F.pairing.equivMapDual e_idx f_fix
  have hidx := indexEquiv_intertwine_of_weightMap e hw
  { pairing := F.pairing.mapDual e_idx f_fix
    base := F.base.map eqv
    rootSystem := inferInstance
    reduced := isReduced_of_equiv eqv
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation x y := mapDual_toLinearMap_apply F.pairing e_idx f_fix x y
    root_eq v := by
      change (f_fix (F.pairing.root (e_idx.symm v)) : M₂) = (v : M₂)
      rw [LinearEquiv.fixedSubmoduleCongr_apply, F.coe_root]
      exact e.weightEquiv.apply_symm_apply v.val
    base_eq v := by
      classical
      rw [F.base.support_map_eq, Finset.mem_image]
      refine ⟨?_, ?_⟩
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨j, hj, hju⟩ := F.mem_support_base_iff.mp hu
        refine ⟨e.indexEquiv j, ?_, ?_⟩
        · rw [← hb, b.support_map_eq]
          exact Finset.mem_image_of_mem _ hj
        · change P₂.orbitSum τ (e.indexEquiv j) = e.weightEquiv (u : M)
          rw [← hju, Equiv.weightEquiv_apply, weightMap_orbitSum e hidx j]
      · rintro ⟨j₂, hj₂, hjv⟩
        rw [← hb, b.support_map_eq, Finset.mem_image] at hj₂
        obtain ⟨j, hj, rfl⟩ := hj₂
        refine ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
          F.orbitSum_mem_support_base hj, Subtype.ext ?_⟩
        change e.weightMap (P.orbitSum σ j) = (v : M₂)
        rw [weightMap_orbitSum e hidx j, hjv] }

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
  exact LinearEquiv.fixedSubmoduleCongr_apply e.weightEquiv hw x

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
