/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Orbit-sum realizations of folded root systems

Let `P` be a root pairing with finitely many roots, `b` a base of `P`, and `σ` an automorphism of
`P`. When `σ` folds `P`, the folded root system lives on the fixed submodule
`LinearMap.fixedSubmodule σ.weightMap` and its linear dual, paired by evaluation, with roots
indexed by the distinct orbit-sum vectors `P.foldedIndices σ` and simple roots given by the orbit
sums of the simple roots of `b`.

This file defines the specification `RootPairing.OrbitSumRealization` of such a folded root system
and proves the structural properties that follow from the specification alone, before any
simply-laced or orthogonality hypothesis is imposed:

* **Uniqueness**: over a characteristic-zero domain, two orbit-sum realizations of `(P, b, σ)` are
  equal (`RootPairing.OrbitSumRealization.instSubsingleton`). Indeed `RootPairing.IsRootSystem.ext`
  identifies the underlying root pairings from the evaluation and root-vector equations, and
  `RootPairing.Base.ext` then identifies the bases from the simple-support equation.
* **Positivity**: when `σ` permutes the simple roots of `b`, a folded root is positive for the
  folded base if and only if it is the orbit sum of a positive root of `b`
  (`RootPairing.OrbitSumRealization.isPos_iff`).
* **Fixed-space simple-orbit frame**: when `P` is a root system and `σ` permutes the simple roots
  of `b`, the simple-orbit sums are linearly independent and, over a characteristic-zero field,
  span the fixed submodule (`RootPairing.linearIndepOn_orbitSum_support`,
  `RootPairing.span_fixedSubmodule_orbitSum_support_eq_top`).
* **Identity fold**: for `σ = 1`, every finite reduced crystallographic root system admits an
  orbit-sum realization isomorphic to `(P, b)` (`RootPairing.OrbitSumRealization.one`,
  `RootPairing.OrbitSumRealization.equivOne`), including in rank zero.
* **Transport along intertwining equivalences**: a based equivalence of root pairings intertwining
  two automorphisms transports orbit-sum realizations and induces a based equivalence between any
  two realizations (`RootPairing.OrbitSumRealization.map`,
  `RootPairing.OrbitSumRealization.equivOfIntertwining`).

## Main definitions

* `RootPairing.foldedIndex`: the folded root index attached to a root index `i` via its orbit sum.
* `RootPairing.OrbitSumRealization`: bundled specification of an orbit-sum fold on the fixed
  submodule and its dual.
* `RootPairing.OrbitSumRealization.one`: the orbit-sum realization of the identity automorphism.
* `RootPairing.OrbitSumRealization.equivOne`: the canonical equivalence from `P` to an orbit-sum
  realization of `1 : P.Aut`.
* `RootPairing.OrbitSumRealization.map`: transport of an orbit-sum realization along an
  intertwining based equivalence.
* `RootPairing.OrbitSumRealization.equivOfIntertwining`: the equivalence between two orbit-sum
  realizations induced by an intertwining equivalence.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: an orbit-sum realization is unique over a
  characteristic-zero domain.
* `RootPairing.OrbitSumRealization.coroot_eq_of_preReflection_mapsTo`: each folded coroot functional
  is uniquely determined by its reflection stability on the folded roots.
* `RootPairing.OrbitSumRealization.isPos_foldedIndex_iff` and
  `RootPairing.OrbitSumRealization.isPos_iff`: folded positivity agrees with original positivity.
* `RootPairing.foldedIndex_eq_iff_mem_orbitIndices_of_mem_support`: two simple roots determine the
  same folded root index if and only if they lie in the same `σ`-orbit.
* `RootPairing.linearIndepOn_orbitSum_support` and
  `RootPairing.span_fixedSubmodule_orbitSum_support_eq_top`: the simple-orbit sums are linearly
  independent and span the fixed submodule.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pages 1--3.
-/

public section

namespace RootPairing

open Finset Function Set Submodule TauCeti

section FoldedIndex

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)

/-- The folded root index attached to `i`, namely its orbit sum viewed in `P.foldedIndices σ`. -/
noncomputable def foldedIndex (i : ι) : P.foldedIndices σ :=
  ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩

@[simp]
theorem coe_foldedIndex (i : ι) :
    ((P.foldedIndex σ i : P.foldedIndices σ) : M) = P.orbitSum σ i := by
  rw [foldedIndex]

theorem foldedIndex_surjective : Surjective (P.foldedIndex σ) := fun u ↦ by
  obtain ⟨i, hi⟩ := P.mem_foldedIndices.mp u.2
  exact ⟨i, Subtype.ext hi⟩

@[simp]
theorem foldedIndex_indexEquiv (i : ι) :
    P.foldedIndex σ (σ.indexEquiv i) = P.foldedIndex σ i :=
  Subtype.ext (P.orbitSum_indexEquiv σ i)

variable {P σ} in
/-- Two indices in the same `σ`-orbit determine the same folded root index. -/
theorem foldedIndex_eq_of_mem {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.foldedIndex σ j = P.foldedIndex σ i :=
  Subtype.ext (P.orbitSum_eq_of_mem h)

/-- Each folded root vector lies in the fixed submodule of `σ.weightMap`. -/
theorem coe_mem_fixedSubmodule (u : P.foldedIndices σ) :
    (u : M) ∈ LinearMap.fixedSubmodule σ.weightMap := by
  obtain ⟨i, hi⟩ := P.mem_foldedIndices.mp u.2
  exact hi ▸ P.orbitSum_mem_fixedSubmodule σ i

variable {P σ} in
/-- If `σ` maps `b.support` into itself, the entire `σ`-orbit of a simple root lies in
`b.support`. -/
theorem mem_support_of_mem_orbitIndices {b : P.Base}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {s k : ι}
    (hs : s ∈ b.support) (hk : k ∈ P.orbitIndices σ s) : k ∈ b.support := by
  obtain ⟨m, rfl⟩ := P.mem_orbitIndices_iff_exists_pow.mp hk
  clear hk
  induction m with
  | zero => exact hs
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hσ _ ih

end FoldedIndex

/-! ### Auxiliary helpers for automorphism powers and pairing pushforwards -/

section Helpers

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

private theorem weightMap_pow_root (P : RootPairing ι R M N) (σ : P.Aut) (t : ℕ) (j : ι) :
    (σ ^ t : P.Aut).weightMap (P.root j) = P.root ((σ.indexEquiv ^ t) j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hmul : (σ ^ (t + 1) : P.Aut).weightMap (P.root j) =
        σ.weightMap ((σ ^ t : P.Aut).weightMap (P.root j)) := by
      rw [pow_succ']
      rfl
    rw [hmul, ih, Hom.root_weightMap_apply, pow_succ', Equiv.Perm.mul_apply]

private theorem weightMap_pow_of_fixed {P : RootPairing ι R M N} {σ : P.Aut} {x : M}
    (hx : σ.weightMap x = x) (t : ℕ) : (σ ^ t : P.Aut).weightMap x = x := by
  induction t with
  | zero => simp
  | succ t ih => simp [pow_succ', Equiv.mul_eq_comp, ih, hx]

/-- The canonical equivalence from `P` to `P.map e f g`. -/
private def equivMap (P : RootPairing ι R M N)
    (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) : P.Equiv (P.map e f g) where
  weightMap := f.toLinearMap
  coweightMap := g.symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by ext; simp [RootPairing.map]
  root_weightMap := by ext; simp [RootPairing.map]
  coroot_coweightMap := by ext; simp [RootPairing.map]
  bijective_weightMap := f.bijective
  bijective_coweightMap := g.symm.bijective

private theorem isReduced_of_equiv {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    [P.IsReduced] (e : P.Equiv Q) : Q.IsReduced where
  eq_or_eq_neg i j hij := by
    obtain ⟨i₀, rfl⟩ := e.indexEquiv.surjective i
    obtain ⟨j₀, rfl⟩ := e.indexEquiv.surjective j
    rw [e.toHom.linearIndependent_root_indexEquiv_iff e.bijective_weightMap.injective] at hij
    rcases IsReduced.eq_or_eq_neg (P := P) i₀ j₀ hij with hpos | hneg
    · refine .inl ?_
      rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, hpos]
    · refine .inr ?_
      rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, hneg, map_neg]

end Helpers

/-! ### Specification of an orbit-sum realization -/

section Realization

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An **orbit-sum realization** of `(P, b, σ)` bundles a reduced crystallographic root system on
the fixed submodule `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, paired by
evaluation, whose roots are the distinct orbit sums `P.foldedIndices σ` and whose simple roots are
the orbit sums of the simple roots of `b`. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι]
    (b : P.Base) (σ : P.Aut) where
  /-- The folded root pairing on the fixed submodule and its linear dual. -/
  pairing : RootPairing (P.foldedIndices σ) R (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- The base of the folded root pairing. -/
  base : pairing.Base
  /-- Both the folded roots and the folded coroots span. -/
  rootSystem : pairing.IsRootSystem
  /-- No two folded roots are proportional except a root and its negative. -/
  reduced : pairing.IsReduced
  /-- All folded root-coroot pairings are integers. -/
  crystallographic : pairing.IsCrystallographic
  /-- The perfect pairing is evaluation against the linear dual of the fixed submodule. -/
  evaluation : ∀ x y, pairing.toLinearMap x y = y x
  /-- Each folded root is its orbit-sum vector in the ambient space. -/
  root_eq : ∀ i, (pairing.root i : M) = (i : M)
  /-- Simple folded roots are exactly the orbit sums of the original simple roots. -/
  base_eq : ∀ i, i ∈ base.support ↔
    ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

attribute [instance] OrbitSumRealization.rootSystem
  OrbitSumRealization.reduced OrbitSumRealization.crystallographic

namespace OrbitSumRealization

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

/-- The bilinear map of an orbit-sum realization is dual evaluation on the fixed submodule. -/
theorem toLinearMap_eq :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) := by
  ext x y
  exact F.evaluation x y

@[simp]
theorem toLinearMap_apply (x : LinearMap.fixedSubmodule σ.weightMap)
    (y : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x y = y x :=
  F.evaluation x y

/-- Each coroot functional `F.pairing.coroot' i` coincides with the dual vector
`F.pairing.coroot i`. -/
theorem coroot'_eq_coroot (i : P.foldedIndices σ) :
    F.pairing.coroot' i = F.pairing.coroot i := by
  ext x
  exact F.evaluation x (F.pairing.coroot i)

@[simp]
theorem coe_root (i : P.foldedIndices σ) : (F.pairing.root i : M) = (i : M) :=
  F.root_eq i

/-- The ambient vector of the folded root at `P.foldedIndex σ j` is `P.orbitSum σ j`. -/
theorem coe_root_foldedIndex (j : ι) :
    (F.pairing.root (P.foldedIndex σ j) : M) = P.orbitSum σ j := by
  rw [F.root_eq, coe_foldedIndex]

/-- The ambient vectors of the folded roots are precisely `P.foldedIndices σ`. -/
theorem range_coe_root :
    range (fun i : P.foldedIndices σ ↦ (F.pairing.root i : M)) = P.foldedIndices σ := by
  ext x
  simp only [Set.mem_range, coe_root]
  exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The folded root index of a simple root of `b` lies in the folded base support. -/
theorem foldedIndex_mem_support_base {j : ι} (hj : j ∈ b.support) :
    P.foldedIndex σ j ∈ F.base.support :=
  (F.base_eq _).mpr ⟨j, hj, (P.coe_foldedIndex σ j).symm⟩

/-- The folded base support is the image of `b.support` under `P.foldedIndex σ`. -/
theorem support_base_eq_image [DecidableEq (P.foldedIndices σ)] :
    F.base.support = b.support.image (P.foldedIndex σ) := by
  ext u
  rw [Finset.mem_image, F.base_eq]
  exact ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext ((P.coe_foldedIndex σ j).trans hju)⟩,
    fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, (P.coe_foldedIndex σ j).symm.trans (congrArg Subtype.val hju)⟩⟩

/-! ### Uniqueness -/

section Uniqueness

variable [CharZero R] [IsDomain R]

/-- Two orbit-sum realizations of `(P, b, σ)` have the same underlying root pairing. -/
theorem pairing_eq (F₁ F₂ : P.OrbitSumRealization b σ) : F₁.pairing = F₂.pairing := by
  refine IsRootSystem.ext (F₁.toLinearMap_eq.trans F₂.toLinearMap_eq.symm) ?_
  ext i : 2
  exact (F₁.root_eq i).trans (F₂.root_eq i).symm

/-- **Uniqueness of an orbit-sum realization.** Over a characteristic-zero domain, the evaluation,
root-vector, and simple-support equations uniquely determine the entire realization, including its
coroot functionals and base. -/
instance instSubsingleton : Subsingleton (P.OrbitSumRealization b σ) where
  allEq F₁ F₂ := by
    have hp : F₁.pairing = F₂.pairing := pairing_eq F₁ F₂
    cases F₁ with | mk p₁ b₁ rs₁ red₁ cr₁ ev₁ rt₁ bs₁ => ?_
    cases F₂ with | mk p₂ b₂ rs₂ red₂ cr₂ ev₂ rt₂ bs₂ => ?_
    subst hp
    congr
    refine Base.ext (Finset.ext fun i ↦ ?_)
    exact (bs₁ i).trans (bs₂ i).symm

/-- Each coroot functional of an orbit-sum realization is uniquely characterized as the dual
functional taking value `2` at `F.pairing.root i` whose pre-reflection preserves the folded root
set. -/
theorem coroot_eq_of_preReflection_mapsTo (i : P.foldedIndices σ)
    {f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)}
    (hf₁ : f (F.pairing.root i) = 2)
    (hf₂ : MapsTo (Module.preReflection (F.pairing.root i) f)
      (range F.pairing.root) (range F.pairing.root)) :
    f = F.pairing.coroot i := by
  have : Module.IsReflexive R (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_isPerfPair F.pairing.toLinearMap
  rw [← F.coroot'_eq_coroot]
  exact Module.Dual.eq_of_preReflection_mapsTo (finite_range F.pairing.root)
    IsRootSystem.span_root_eq_top hf₁ hf₂
    (F.pairing.coroot_root_two i) (F.pairing.mapsTo_reflection_root i)

end Uniqueness

/-! ### Positivity and positive-root lifts -/

section Positivity

variable [CharZero R]

/-- Averaging a positive root expansion over the period of `σ.indexEquiv` expresses a positive
natural multiple of `F.pairing.root (P.foldedIndex σ j)` in the folded positive root cone. -/
private theorem nsmul_root_foldedIndex_mem_posRootCone {j : ι} (hj : b.IsPos j) :
    ∃ d : ℕ, 0 < d ∧
      d • F.pairing.root (P.foldedIndex σ j) ∈ posRootCone F.pairing F.base := by
  have := Fintype.ofFinite ι
  let m : ℕ := orderOf σ.indexEquiv
  have hper (k : ι) : (σ.indexEquiv ^ m) k = k := by
    rw [orderOf_dvd_iff_pow_eq_one.mp dvd_rfl, Equiv.Perm.coe_one, id_eq]
  obtain ⟨n, -, hn⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b j).mpr hj)
  have hsum : (m / #(P.orbitIndices σ j)) • P.orbitSum σ j =
      ∑ k ∈ b.support, (n k * (m / #(P.orbitIndices σ k))) • P.orbitSum σ k := by
    rw [← P.sum_range_root_pow_apply_eq_nsmul (hper j)]
    have hpow (t : ℕ) : P.root ((σ.indexEquiv ^ t) j) =
        ∑ k ∈ b.support, n k • P.root ((σ.indexEquiv ^ t) k) := by
      rw [← weightMap_pow_root P σ t j, hn, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_nsmul, weightMap_pow_root]
    simp_rw [hpow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.smul_sum, P.sum_range_root_pow_apply_eq_nsmul (hper k), mul_smul]
  refine ⟨m / #(P.orbitIndices σ j),
    Nat.div_pos (Nat.le_of_dvd (orderOf_pos σ.indexEquiv) (P.card_orbitIndices_dvd (hper j)))
      (P.card_orbitIndices_pos σ j), ?_⟩
  have hlift : (m / #(P.orbitIndices σ j)) • F.pairing.root (P.foldedIndex σ j) =
      ∑ k ∈ b.support, (n k * (m / #(P.orbitIndices σ k))) •
        F.pairing.root (P.foldedIndex σ k) :=
    Subtype.ext (by simpa using hsum)
  rw [hlift]
  refine sum_mem fun k hk ↦ nsmul_mem ((mem_posRootCone F.pairing F.base).mpr ?_) _
  classical
  exact ⟨Pi.single (P.foldedIndex σ k) 1, by
    simp [Pi.single_apply, F.foldedIndex_mem_support_base hk]⟩

/-- A positive root `j` of `b` maps to a positive root `P.foldedIndex σ j` of `F.base`. -/
private theorem isPos_foldedIndex_of_isPos {j : ι} (hj : b.IsPos j) :
    F.base.IsPos (P.foldedIndex σ j) := by
  obtain ⟨d, hd, hcone⟩ := F.nsmul_root_foldedIndex_mem_posRootCone hj
  by_contra hneg
  have hneg_cone : F.pairing.root (F.pairing.reflectionPerm (P.foldedIndex σ j)
      (P.foldedIndex σ j)) ∈ posRootCone F.pairing F.base :=
    root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr
      ((isPos_reflectionPerm_self_iff_mem_negRoots _ _ _).mpr ((mem_negRoots _ _ _).mpr hneg)))
  rw [root_reflectionPerm, reflection_apply_self] at hneg_cone
  have hzero : d • F.pairing.root (P.foldedIndex σ j) = 0 :=
    eq_zero_of_add_eq_zero_of_mem_posRootCone F.pairing F.base hcone
      (nsmul_mem hneg_cone d) (by rw [smul_neg, add_neg_cancel])
  have htwo := congrArg (F.pairing.coroot' (P.foldedIndex σ j)) hzero
  rw [map_nsmul, root_coroot'_eq_pairing, pairing_same, map_zero, nsmul_eq_mul,
    ← Nat.cast_ofNat, ← Nat.cast_mul, Nat.cast_eq_zero] at htwo
  omega

/-- **Folded positivity on indexed orbit sums.** For any `j : ι`, `P.foldedIndex σ j` is positive
for `F.base` if and only if `j` is positive for `b`. -/
theorem isPos_foldedIndex_iff (j : ι) :
    F.base.IsPos (P.foldedIndex σ j) ↔ b.IsPos j := by
  refine ⟨fun h ↦ ?_, F.isPos_foldedIndex_of_isPos⟩
  by_contra hj
  have hj' : b.IsPos (P.reflectionPerm j j) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b j).mpr ((mem_negRoots P b j).mpr hj)
  have hfold : P.foldedIndex σ (P.reflectionPerm j j) =
      F.pairing.reflectionPerm (P.foldedIndex σ j) (P.foldedIndex σ j) := by
    refine F.pairing.root.injective (Subtype.ext ?_)
    simp [F.coe_root_foldedIndex, P.orbitSum_reflectionPerm_self, root_reflectionPerm]
  have hpos' := F.isPos_foldedIndex_of_isPos hj'
  rw [hfold, isPos_reflectionPerm_self_iff_mem_negRoots, mem_negRoots] at hpos'
  exact hpos' h

/-- **Positive-root lifting.** Every positive folded root is the orbit sum of a positive original
root, and conversely every positive original root has a positive orbit sum. -/
theorem isPos_iff (u : P.foldedIndices σ) :
    F.base.IsPos u ↔ ∃ j, b.IsPos j ∧ P.orbitSum σ j = (u : M) := by
  obtain ⟨j₀, rfl⟩ := P.foldedIndex_surjective σ u
  refine ⟨fun hu ↦ ⟨j₀, F.isPos_foldedIndex_iff j₀ |>.mp hu, P.coe_foldedIndex σ j₀⟩, ?_⟩
  rintro ⟨j, hj, hju⟩
  have heq : P.foldedIndex σ j = P.foldedIndex σ j₀ :=
    Subtype.ext ((P.coe_foldedIndex σ j).trans hju)
  rw [← heq]
  exact (F.isPos_foldedIndex_iff j).mpr hj

end Positivity

end OrbitSumRealization

end Realization

/-! ### Linear independence and spanning of simple-orbit sums -/

section SimpleOrbitFrame

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem]

variable {P} in
/-- In the simple-root basis `b.toWeightBasis`, the `s`-coordinate of a simple-orbit sum
`P.orbitSum σ s'` is `1` if `s` belongs to the `σ`-orbit of `s'` and `0` otherwise. -/
theorem toWeightBasis_repr_orbitSum_of_mem_support [DecidableEq ι] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {s s' : ι}
    (hs : s ∈ b.support) (hs' : s' ∈ b.support) :
    b.toWeightBasis.repr (P.orbitSum σ s') ⟨s, hs⟩ =
      if s ∈ P.orbitIndices σ s' then 1 else 0 := by
  rw [P.orbitSum_def, map_sum, Finsupp.finsetSum_apply]
  have hterm (x : ι) (hx : x ∈ P.orbitIndices σ s') :
      b.toWeightBasis.repr (P.root x) ⟨s, hs⟩ = if x = s then 1 else 0 := by
    have hxb : x ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs' hx
    have hroot : P.root x = b.toWeightBasis ⟨x, hxb⟩ := (b.toWeightBasis_apply ⟨x, hxb⟩).symm
    rw [hroot, Module.Basis.repr_self, Finsupp.single_apply]
    simp [Subtype.ext_iff, eq_comm]
  rw [Finset.sum_congr rfl hterm]
  by_cases hmem : s ∈ P.orbitIndices σ s'
  · rw [ite_eq_left_iff.mpr fun h ↦ (h hmem).elim, Finset.sum_ite_eq' (P.orbitIndices σ s') s,
      ite_eq_left_iff.mpr fun h ↦ (h hmem).elim]
  · rw [ite_eq_right_iff.mpr fun h ↦ (hmem h).elim]
    exact Finset.sum_eq_zero fun x hx ↦
      ite_eq_right_iff.mpr fun hxs ↦ (hmem (hxs ▸ hx)).elim

variable {P} in
/-- Two simple roots of `b` determine the same folded root index if and only if they lie in the
same `σ`-orbit. -/
theorem foldedIndex_eq_iff_mem_orbitIndices_of_mem_support [Nontrivial R] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {s s' : ι}
    (hs : s ∈ b.support) (hs' : s' ∈ b.support) :
    P.foldedIndex σ s = P.foldedIndex σ s' ↔ s ∈ P.orbitIndices σ s' := by
  classical
  refine ⟨fun h ↦ ?_, P.foldedIndex_eq_of_mem⟩
  have heq : P.orbitSum σ s = P.orbitSum σ s' := by
    simpa [coe_foldedIndex] using congrArg Subtype.val h
  have hrepr := congrArg (fun v ↦ b.toWeightBasis.repr v ⟨s, hs⟩) heq
  rw [P.toWeightBasis_repr_orbitSum_of_mem_support hσ hs hs,
    P.toWeightBasis_repr_orbitSum_of_mem_support hσ hs hs'] at hrepr
  simp only [P.self_mem_orbitIndices σ s, ↓reduceIte] at hrepr
  by_contra hnot
  simp only [hnot, ↓reduceIte] at hrepr
  exact one_ne_zero hrepr

/-- The simple-orbit sums of a based automorphism are linearly independent over `R`, because
distinct simple orbits have disjoint supports in the simple-root basis `b.toWeightBasis`. -/
theorem linearIndepOn_orbitSum_support {b : P.Base} {σ : P.Aut}
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) :
    LinearIndepOn R (fun u : P.foldedIndices σ ↦ (u : M))
      (P.foldedIndex σ '' (b.support : Set ι)) := by
  nontriviality R
  classical
  rw [linearIndepOn_iff']
  intro t c htsub hsum u hu
  obtain ⟨s, hs, rfl⟩ := htsub (Finset.mem_coe.mpr hu)
  have hrepr := congrArg (fun x ↦ b.toWeightBasis.repr x ⟨s, hs⟩) hsum
  rw [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.zero_apply] at hrepr
  have hcoord (v : P.foldedIndices σ) (hv : v ∈ t) :
      b.toWeightBasis.repr (c v • (v : M)) ⟨s, hs⟩ =
        if v = P.foldedIndex σ s then c v else 0 := by
    obtain ⟨s', hs', rfl⟩ := htsub (Finset.mem_coe.mpr hv)
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coe_foldedIndex,
      P.toWeightBasis_repr_orbitSum_of_mem_support hσ hs hs']
    by_cases hvs : P.foldedIndex σ s' = P.foldedIndex σ s
    · have hmem : s ∈ P.orbitIndices σ s' :=
        (P.foldedIndex_eq_iff_mem_orbitIndices_of_mem_support hσ hs hs').mp hvs.symm
      simp [hvs, hmem]
    · have hmem : s ∉ P.orbitIndices σ s' := fun hm ↦
        hvs ((P.foldedIndex_eq_iff_mem_orbitIndices_of_mem_support hσ hs hs').mpr hm).symm
      simp [hvs, hmem]
  rw [Finset.sum_congr rfl hcoord, Finset.sum_ite_eq' t (P.foldedIndex σ s)] at hrepr
  simpa [hu] using hrepr

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]

/-- The simple-orbit sums span the fixed submodule `LinearMap.fixedSubmodule σ.weightMap`. -/
theorem span_fixedSubmodule_orbitSum_support_eq_top (b : P.Base) (σ : P.Aut) :
    span K ((fun j : b.support ↦
      (⟨P.orbitSum σ j, P.orbitSum_mem_fixedSubmodule σ j⟩ :
        LinearMap.fixedSubmodule σ.weightMap)) '' univ) = ⊤ := by
  have := Fintype.ofFinite ι
  let m : ℕ := orderOf σ.indexEquiv
  have hm : 0 < m := orderOf_pos σ.indexEquiv
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hper (k : ι) : (σ.indexEquiv ^ m) k = k := by
    rw [orderOf_dvd_iff_pow_eq_one.mp dvd_rfl, Equiv.Perm.coe_one, id_eq]
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxpow := weightMap_pow_of_fixed (LinearMap.mem_fixedSubmodule_iff.mp hx)
  have hrepr : x = ∑ s : b.support, b.toWeightBasis.repr x s • P.root s := by
    simpa using (b.toWeightBasis.sum_repr x).symm
  have hsum : (m : K) • x =
      ∑ s : b.support,
        (b.toWeightBasis.repr x s * (m / #(P.orbitIndices σ s) : ℕ)) • P.orbitSum σ s := by
    calc (m : K) • x
        = ∑ t ∈ range m, (σ ^ t : P.Aut).weightMap x := by
            simp [hxpow, Nat.cast_smul_eq_nsmul]
      _ = ∑ t ∈ range m, ∑ s : b.support,
            b.toWeightBasis.repr x s • P.root ((σ.indexEquiv ^ t) s) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            conv_lhs => rw [hrepr]
            rw [map_sum]
            exact Finset.sum_congr rfl fun s _ ↦ by rw [map_smul, weightMap_pow_root]
      _ = ∑ s : b.support, b.toWeightBasis.repr x s •
            ∑ t ∈ range m, P.root ((σ.indexEquiv ^ t) s) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ ↦ (Finset.smul_sum ..).symm
      _ = ∑ s : b.support,
            (b.toWeightBasis.repr x s * (m / #(P.orbitIndices σ s) : ℕ)) • P.orbitSum σ s := by
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [P.sum_range_root_pow_apply_eq_nsmul (hper s), ← Nat.cast_smul_eq_nsmul K, smul_smul]
  have hvec : (⟨x, hx⟩ : LinearMap.fixedSubmodule σ.weightMap) =
      ∑ s : b.support,
        ((m : K)⁻¹ * (b.toWeightBasis.repr x s * (m / #(P.orbitIndices σ s) : ℕ))) •
          (⟨P.orbitSum σ s, P.orbitSum_mem_fixedSubmodule σ s⟩ :
            LinearMap.fixedSubmodule σ.weightMap) := by
    apply Subtype.ext
    calc x = (m : K)⁻¹ • ((m : K) • x) := by rw [inv_smul_smul₀ hmK]
      _ = _ := by
        rw [hsum, Finset.smul_sum]
        simp [smul_smul]
  rw [hvec]
  exact sum_mem fun s _ ↦ smul_mem _ _ (subset_span ⟨s, mem_univ s, rfl⟩)

end Field

end SimpleOrbitFrame

/-! ### The identity automorphism -/

section One

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The bijection from `ι` to `P.foldedIndices (1 : P.Aut)` sending `i` to `P.foldedIndex 1 i`. -/
private noncomputable def foldedIndicesOneEquiv (P : RootPairing ι R M N) [Finite ι] :
    ι ≃ P.foldedIndices (1 : P.Aut) :=
  _root_.Equiv.ofBijective (P.foldedIndex 1)
    ⟨fun _ _ h ↦ P.root.injective (by simpa using congrArg Subtype.val h),
      P.foldedIndex_surjective 1⟩

/-- The linear isomorphism between `M` and the fixed submodule of `(1 : P.Aut).weightMap`. -/
private def fixedSubmoduleOneEquiv (P : RootPairing ι R M N) :
    M ≃ₗ[R] LinearMap.fixedSubmodule (1 : P.Aut).weightMap where
  toFun m := ⟨m, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

namespace OrbitSumRealization

/-- **Identity orbit-sum realization.** For the identity automorphism `1 : P.Aut`, every finite
reduced crystallographic root system admits an orbit-sum realization isomorphic to `(P, b)`,
including the empty root system on the zero space. -/
noncomputable def one (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    P.OrbitSumRealization b 1 :=
  let eM := fixedSubmoduleOneEquiv P
  let eN : N ≃ₗ[R] Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :=
    (eM.dualMap.trans P.flip.toPerfPair.symm).symm
  let eι := foldedIndicesOneEquiv P
  let e := equivMap P eι eM eN
  { pairing := P.map eι eM eN
    base := b.map e
    rootSystem := inferInstance
    reduced := isReduced_of_equiv e
    crystallographic := e.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by
      have hx : e.weightEquiv (eM.symm x) = x := eM.apply_symm_apply x
      have hy : e.coweightEquiv y = P.toLinearMap.flip.toPerfPair.symm (eM.dualMap y) := rfl
      rw [← hx, e.toLinearMap_weightEquiv, hy, P.toLinearMap.apply_toPerfPair_flip, hx]
      exact congrArg y (eM.apply_symm_apply x)
    root_eq := fun u ↦ by
      obtain ⟨j, rfl⟩ := eι.surjective u
      have hj : (eι j : M) = P.root j := by
        have : eι j = P.foldedIndex 1 j := rfl
        rw [this, P.coe_foldedIndex, P.orbitSum_one]
      have hr : (P.map eι eM eN).root (e.indexEquiv j) = e.weightMap (P.root j) :=
        (Hom.root_weightMap_apply P _ j e.toHom).symm
      exact (congrArg Subtype.val hr).trans hj.symm
    base_eq := fun u ↦ by
      classical
      rw [b.support_map_eq e, Finset.mem_image]
      have he (j : ι) : (e.indexEquiv j : M) = P.root j := by
        have : e.indexEquiv j = P.foldedIndex 1 j := rfl
        rw [this, P.coe_foldedIndex, P.orbitSum_one]
      refine ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, by rw [← hju, he, P.orbitSum_one]⟩,
        fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext (by rw [he, ← P.orbitSum_one j, hju])⟩⟩ }

/-- The canonical equivalence from `P` to any orbit-sum realization `F` of `1 : P.Aut`, acting as
the identity on ambient weight vectors. -/
noncomputable def equivOne {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) : P.Equiv F.pairing :=
  Equiv.mk' P F.pairing (fixedSubmoduleOneEquiv P) (foldedIndicesOneEquiv P) fun i ↦
    Subtype.ext <| by
      have hi : (foldedIndicesOneEquiv P) i = P.foldedIndex 1 i := rfl
      rw [hi, F.coe_root_foldedIndex, P.orbitSum_one]
      rfl

/-- The weight equivalence `F.equivOne` embeds `M` as the identity into the ambient module. -/
theorem coe_equivOne_weightMap {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) (x : M) :
    (F.equivOne.weightMap x : M) = x := by
  rfl

@[simp]
theorem equivOne_indexEquiv {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) (i : ι) :
    F.equivOne.indexEquiv i = P.foldedIndex 1 i := by
  rfl

@[simp]
theorem map_equivOne {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) :
    b.map F.equivOne = F.base := by
  classical
  refine Base.ext (Finset.ext fun u ↦ ?_)
  rw [b.support_map_eq F.equivOne, Finset.mem_image, F.base_eq]
  refine ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, by simpa using congrArg Subtype.val hju⟩,
    fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext (by simpa using hju)⟩⟩

end OrbitSumRealization

end One

/-! ### Transport along intertwining equivalences -/

section Intertwining

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}

/-- If an equivalence `e : P.Equiv P₂` of root systems intertwines `σ` and `τ` on root indices, it
intertwines their weight-space actions. -/
theorem Equiv.weightMap_aut_of_indexEquiv [P.IsRootSystem] (e : P.Equiv P₂) {σ : P.Aut}
    {τ : P₂.Aut} (h : ∀ j, e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j))
    (x : M) : e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x) := by
  have hlin : e.weightMap ∘ₗ σ.weightMap = τ.weightMap ∘ₗ e.weightMap :=
    LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun j ↦ by
      simp only [LinearMap.comp_apply, Hom.root_weightMap_apply, h j]
  exact LinearMap.congr_fun hlin x

/-- If `e : P.Equiv P₂` intertwines `σ.weightMap` and `τ.weightMap`, it intertwines `σ.indexEquiv`
and `τ.indexEquiv`. -/
theorem Equiv.indexEquiv_aut_of_weightMap (e : P.Equiv P₂) {σ : P.Aut} {τ : P₂.Aut}
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) (j : ι) :
    e.indexEquiv (σ.indexEquiv j) = τ.indexEquiv (e.indexEquiv j) := by
  apply P₂.root.injective
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, he, Hom.root_weightMap_apply,
    Hom.root_weightMap_apply]

variable [Finite ι] [Finite ι₂]

/-- The bijection `P.foldedIndices σ ≃ P₂.foldedIndices τ` induced by an intertwining equivalence
`e : P.Equiv P₂`. -/
private noncomputable def foldedIndicesEquivOfIntertwining (e : P.Equiv P₂) {σ : P.Aut}
    {τ : P₂.Aut} (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ :=
  have hidx := e.indexEquiv_aut_of_weightMap he
  { toFun u := ⟨e.weightMap (u : M), P₂.mem_foldedIndices.mpr <| by
      obtain ⟨j, hj⟩ := P.mem_foldedIndices.mp u.2
      exact ⟨e.indexEquiv j, by rw [← hj, P.weightMap_orbitSum e hidx j]⟩⟩
    invFun v := ⟨e.weightEquiv.symm (v : M₂), P.mem_foldedIndices.mpr <| by
      obtain ⟨k, hk⟩ := P₂.mem_foldedIndices.mp v.2
      refine ⟨e.indexEquiv.symm k, ?_⟩
      apply e.bijective_weightMap.injective
      rw [P.weightMap_orbitSum e hidx, _root_.Equiv.apply_symm_apply, e.weightMap_weightEquiv_symm,
        hk]⟩
    left_inv u := Subtype.ext (e.weightEquiv_symm_weightMap (u : M))
    right_inv v := Subtype.ext (e.weightMap_weightEquiv_symm (v : M₂)) }

/-- The linear equivalence between fixed submodules induced by an intertwining equivalence
`e : P.Equiv P₂`. -/
private noncomputable def fixedSubmoduleEquivOfIntertwining (e : P.Equiv P₂) {σ : P.Aut}
    {τ : P₂.Aut} (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R] LinearMap.fixedSubmodule τ.weightMap where
  toFun x := ⟨e.weightMap x.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    rw [← he, LinearMap.mem_fixedSubmodule_iff.mp x.2]⟩
  map_add' x y := Subtype.ext (map_add e.weightMap x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul e.weightMap c x.1)
  invFun y := ⟨e.weightEquiv.symm y.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    apply e.bijective_weightMap.injective
    rw [he, e.weightMap_weightEquiv_symm, LinearMap.mem_fixedSubmodule_iff.mp y.2]⟩
  left_inv x := Subtype.ext (e.weightEquiv_symm_weightMap x.1)
  right_inv y := Subtype.ext (e.weightMap_weightEquiv_symm y.1)

namespace OrbitSumRealization

/-- Transport an orbit-sum realization along a based equivalence `e : P.Equiv P₂` intertwining `σ`
and `τ`. -/
noncomputable def map {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    P₂.OrbitSumRealization b₂ τ :=
  let eM := fixedSubmoduleEquivOfIntertwining e he
  let eN := eM.symm.dualMap
  let eι := foldedIndicesEquivOfIntertwining e he
  let eqv := equivMap F.pairing eι eM eN
  { pairing := F.pairing.map eι eM eN
    base := F.base.map eqv
    rootSystem := inferInstance
    reduced := isReduced_of_equiv eqv
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by simp [RootPairing.map, eN, eM]
    root_eq := fun v ↦ by
      obtain ⟨u, rfl⟩ := eι.surjective v
      simp [RootPairing.map, eM, fixedSubmoduleEquivOfIntertwining,
        eι, foldedIndicesEquivOfIntertwining]
    base_eq := fun v ↦ by
      classical
      have hidx := e.indexEquiv_aut_of_weightMap he
      rw [F.base.support_map_eq eqv, Finset.mem_image]
      refine ⟨fun ⟨u, hu, huv⟩ ↦ ?_, fun ⟨k, hk, hkv⟩ ↦ ?_⟩
      · obtain ⟨j, hj, hju⟩ := (F.base_eq u).mp hu
        refine ⟨e.indexEquiv j, (hbase j).mpr hj, ?_⟩
        rw [← P.weightMap_orbitSum e hidx j, hju]
        simpa [eqv, equivMap, eι, foldedIndicesEquivOfIntertwining] using congrArg Subtype.val huv
      · obtain ⟨j, rfl⟩ := e.indexEquiv.surjective k
        have hj : j ∈ b.support := (hbase j).mp hk
        refine ⟨P.foldedIndex σ j, F.foldedIndex_mem_support_base hj, Subtype.ext ?_⟩
        simpa [eqv, equivMap, eι, foldedIndicesEquivOfIntertwining,
          P.weightMap_orbitSum e hidx j] using hkv }

/-- **Equivalence of realizations induced by an intertwining equivalence.** Over a
characteristic-zero domain, an equivalence `e : P.Equiv P₂` intertwining `σ` and `τ` induces an
equivalence `F.pairing.Equiv F₂.pairing` carrying each fixed vector and orbit-sum index to its
image under `e.weightMap`. -/
noncomputable def equivOfIntertwining [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.pairing.Equiv F₂.pairing :=
  Equiv.mk' F.pairing F₂.pairing (fixedSubmoduleEquivOfIntertwining e he)
    (foldedIndicesEquivOfIntertwining e he) fun u ↦
    Subtype.ext (by simp [fixedSubmoduleEquivOfIntertwining, foldedIndicesEquivOfIntertwining])

@[simp]
theorem coe_equivOfIntertwining_weightMap [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((F.equivOfIntertwining F₂ e he).weightMap x :
      LinearMap.fixedSubmodule τ.weightMap) : M₂) = e.weightMap (x : M) := by
  simp [equivOfIntertwining, Equiv.mk', fixedSubmoduleEquivOfIntertwining]

@[simp]
theorem coe_equivOfIntertwining_indexEquiv [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (u : P.foldedIndices σ) :
    (((F.equivOfIntertwining F₂ e he).indexEquiv u : P₂.foldedIndices τ) : M₂) =
      e.weightMap (u : M) := by
  simp [equivOfIntertwining, Equiv.mk', foldedIndicesEquivOfIntertwining]

@[simp]
theorem map_equivOfIntertwining [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.base.map (F.equivOfIntertwining F₂ e he) = F₂.base := by
  classical
  have hidx := e.indexEquiv_aut_of_weightMap he
  refine Base.ext (Finset.ext fun v ↦ ?_)
  rw [F.base.support_map_eq (F.equivOfIntertwining F₂ e he), Finset.mem_image, F₂.base_eq]
  refine ⟨fun ⟨u, hu, huv⟩ ↦ ?_, fun ⟨k, hk, hkv⟩ ↦ ?_⟩
  · obtain ⟨j, hj, hju⟩ := (F.base_eq u).mp hu
    refine ⟨e.indexEquiv j, (hbase j).mpr hj, ?_⟩
    rw [← P.weightMap_orbitSum e hidx j, hju]
    simpa using congrArg Subtype.val huv
  · obtain ⟨j, rfl⟩ := e.indexEquiv.surjective k
    refine ⟨P.foldedIndex σ j, F.foldedIndex_mem_support_base ((hbase j).mp hk), Subtype.ext ?_⟩
    simpa [P.weightMap_orbitSum e hidx j] using hkv

end OrbitSumRealization

end Intertwining

end RootPairing
