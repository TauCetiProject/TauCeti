/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.LinearAlgebra.FixedSubmodule
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
  `RootPairing.Base.ext` then identifies the bases from the simple-support characterization.
* **Positivity**: over a characteristic-zero ring, a folded root is positive for the folded base if
  and only if it is the orbit sum of a positive root of `b`
  (`RootPairing.OrbitSumRealization.isPos_iff`).
* **Identity fold**: for `σ = 1` over any commutative ring, every finite reduced crystallographic
  root system admits an orbit-sum realization isomorphic to `(P, b)`
  (`RootPairing.OrbitSumRealization.one`, `RootPairing.OrbitSumRealization.oneEquiv`), including in
  rank zero; over a characteristic-zero domain, `RootPairing.OrbitSumRealization.equivOne` gives the
  canonical equivalence to any orbit-sum realization of `1`.
* **Transport along intertwining equivalences**: over any commutative ring, a based equivalence of
  root pairings intertwining two automorphisms transports orbit-sum realizations along an induced
  based equivalence (`RootPairing.OrbitSumRealization.map`,
  `RootPairing.OrbitSumRealization.mapEquiv`); over a characteristic-zero domain, an intertwining
  equivalence induces an equivalence between any two realizations, carrying the base when the
  equivalence is based (`RootPairing.OrbitSumRealization.equivOfIntertwining`,
  `RootPairing.OrbitSumRealization.baseMap_equivOfIntertwining`).

## Main definitions

* `RootPairing.OrbitSumRealization`: bundled specification of an orbit-sum fold on the fixed
  submodule and its dual.
* `RootPairing.OrbitSumRealization.one` and `RootPairing.OrbitSumRealization.oneEquiv`: the
  orbit-sum realization of `1 : P.Aut` and its equivalence with `P` over any commutative ring.
* `RootPairing.OrbitSumRealization.equivOne`: the canonical equivalence from `P` to any orbit-sum
  realization of `1 : P.Aut` over a characteristic-zero domain.
* `RootPairing.OrbitSumRealization.map` and `RootPairing.OrbitSumRealization.mapEquiv`: transport of
  an orbit-sum realization along an intertwining based equivalence over any commutative ring.
* `RootPairing.OrbitSumRealization.equivOfIntertwining`: the equivalence between any two orbit-sum
  realizations induced by an intertwining equivalence over a characteristic-zero domain.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: an orbit-sum realization is unique over a
  characteristic-zero domain.
* `RootPairing.OrbitSumRealization.coroot_eq_of_preReflection_mapsTo`: each folded coroot functional
  is uniquely determined by its reflection stability on the folded roots.
* `RootPairing.OrbitSumRealization.isPos_foldedIndex_iff` and
  `RootPairing.OrbitSumRealization.isPos_iff`: folded positivity agrees with original positivity
  over a characteristic-zero ring.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, pages 1--3.
-/

public section

namespace RootPairing

open Finset Function Set Submodule TauCeti

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
  mem_support_base_iff : ∀ i, i ∈ base.support ↔
    ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

attribute [instance] OrbitSumRealization.rootSystem
  OrbitSumRealization.reduced OrbitSumRealization.crystallographic
attribute [simp] OrbitSumRealization.evaluation OrbitSumRealization.root_eq

namespace OrbitSumRealization

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

/-- The bilinear map of an orbit-sum realization is dual evaluation on the fixed submodule. -/
theorem toLinearMap_eq :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) := by
  ext x y
  exact F.evaluation x y

/-- Each coroot functional `F.pairing.coroot' i` coincides with the dual vector
`F.pairing.coroot i`. -/
theorem coroot'_eq_coroot (i : P.foldedIndices σ) :
    F.pairing.coroot' i = F.pairing.coroot i := by
  ext x
  exact F.evaluation x (F.pairing.coroot i)

/-- The ambient vector of the folded root at `P.foldedIndex σ j` is `P.orbitSum σ j`. -/
theorem coe_root_foldedIndex (j : ι) :
    (F.pairing.root (P.foldedIndex σ j) : M) = P.orbitSum σ j := by
  rw [F.root_eq, coe_foldedIndex]

/-- The ambient vectors of the folded roots are precisely `P.foldedIndices σ`. -/
theorem range_coe_root :
    range (fun i : P.foldedIndices σ ↦ (F.pairing.root i : M)) = P.foldedIndices σ := by
  ext x
  simp only [Set.mem_range, F.root_eq]
  exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- The folded root index of a simple root of `b` lies in the folded base support. -/
theorem foldedIndex_mem_support_base {j : ι} (hj : j ∈ b.support) :
    P.foldedIndex σ j ∈ F.base.support :=
  (F.mem_support_base_iff _).mpr ⟨j, hj, (P.coe_foldedIndex σ j).symm⟩

/-- The folded base support is the image of `b.support` under `P.foldedIndex σ`. -/
theorem support_base_eq_image [DecidableEq (P.foldedIndices σ)] :
    F.base.support = b.support.image (P.foldedIndex σ) := by
  ext u
  rw [Finset.mem_image, F.mem_support_base_iff]
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
    F.pairing.coroot i = f := by
  have : Module.IsReflexive R (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_isPerfPair F.pairing.toLinearMap
  rw [← F.coroot'_eq_coroot]
  exact (Module.Dual.eq_of_preReflection_mapsTo (finite_range F.pairing.root)
    IsRootSystem.span_root_eq_top hf₁ hf₂
    (F.pairing.coroot_root_two i) (F.pairing.mapsTo_reflection_root i)).symm

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
      rw [← Equiv.weightMap_pow_root σ t j, hn, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_nsmul, Equiv.weightMap_pow_root]
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
@[simp]
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
  refine ⟨fun hu ↦ ⟨j₀, (F.isPos_foldedIndex_iff j₀).mp hu, (P.coe_foldedIndex σ j₀).symm⟩, ?_⟩
  rintro ⟨j, hj, hju⟩
  have heq : P.foldedIndex σ j = P.foldedIndex σ j₀ :=
    Subtype.ext ((P.coe_foldedIndex σ j).trans hju)
  rw [← heq, F.isPos_foldedIndex_iff]
  exact hj

end Positivity

end OrbitSumRealization

end Realization

/-! ### The identity automorphism -/

section One

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The bijection from `ι` to `P.foldedIndices (1 : P.Aut)` sending `i` to `P.foldedIndex 1 i`. -/
private noncomputable def foldedIndicesOneEquiv (P : RootPairing ι R M N) [Finite ι] :
    ι ≃ P.foldedIndices (1 : P.Aut) :=
  _root_.Equiv.ofBijective (P.foldedIndex 1)
    ⟨fun _ _ h ↦ P.root.injective (by simpa using congrArg Subtype.val h),
      P.foldedIndex_surjective 1⟩

private theorem foldedIndicesOneEquiv_apply (P : RootPairing ι R M N) [Finite ι] (i : ι) :
    foldedIndicesOneEquiv P i = P.foldedIndex 1 i :=
  _root_.Equiv.ofBijective_apply _ _ i

/-- The linear isomorphism between `M` and the fixed submodule of `(1 : P.Aut).weightMap`. -/
private def fixedSubmoduleOneEquiv (P : RootPairing ι R M N) :
    M ≃ₗ[R] LinearMap.fixedSubmodule (1 : P.Aut).weightMap where
  toFun m := ⟨m, LinearMap.mem_fixedSubmodule_iff.mpr (by simp)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  invFun x := x
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

private theorem coe_fixedSubmoduleOneEquiv_apply (P : RootPairing ι R M N) (m : M) :
    (fixedSubmoduleOneEquiv P m : M) = m :=
  (rfl)

namespace OrbitSumRealization

/-- **Identity orbit-sum realization.** For the identity automorphism `1 : P.Aut`, every finite
reduced crystallographic root system admits an orbit-sum realization isomorphic to `(P, b)`,
including the empty root system on the zero space. -/
noncomputable def one (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    P.OrbitSumRealization b 1 :=
  let eM := fixedSubmoduleOneEquiv P
  let eN : N ≃ₗ[R] Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :=
    (eM.dualMap.trans P.toLinearMap.flip.toPerfPair.symm).symm
  let eι := foldedIndicesOneEquiv P
  let e := P.equivMap eι eM eN
  { pairing := P.map eι eM eN
    base := b.map e
    rootSystem := inferInstance
    reduced := e.isReduced
    crystallographic := e.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by
      have hx : e.weightEquiv (eM.symm x) = x := by
        rw [Equiv.weightEquiv_apply, equivMap_weightMap, LinearEquiv.coe_coe, eM.apply_symm_apply]
      have hy : e.coweightEquiv y = P.toLinearMap.flip.toPerfPair.symm (eM.dualMap y) := by
        rw [Equiv.coweightEquiv_apply, equivMap_coweightMap, LinearEquiv.coe_coe,
          LinearEquiv.symm_symm, LinearEquiv.trans_apply]
      rw [← hx, e.toLinearMap_weightEquiv, hy, P.toLinearMap.apply_toPerfPair_flip,
        LinearEquiv.dualMap_apply, eM.apply_symm_apply, hx]
    root_eq := fun u ↦ by
      obtain ⟨j, rfl⟩ := eι.surjective u
      have hr := (e.toHom.root_weightMap_apply P (P.map eι eM eN) j).symm
      rw [equivMap_indexEquiv, equivMap_weightMap, LinearEquiv.coe_coe] at hr
      rw [hr, coe_fixedSubmoduleOneEquiv_apply, foldedIndicesOneEquiv_apply, P.coe_foldedIndex,
        P.orbitSum_one]
    mem_support_base_iff := fun u ↦ by
      classical
      rw [b.support_map_eq e, Finset.mem_image]
      simp only [e, equivMap_indexEquiv, eι, foldedIndicesOneEquiv_apply, P.orbitSum_one]
      exact ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, by rw [← hju, P.coe_foldedIndex, P.orbitSum_one]⟩,
        fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext (by rw [P.coe_foldedIndex, P.orbitSum_one, hju])⟩⟩ }

/-- The canonical equivalence from `P` to `(one P b).pairing` over any commutative ring, acting as
the identity on ambient weight vectors. -/
noncomputable def oneEquiv (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    P.Equiv (one P b).pairing :=
  P.equivMap (foldedIndicesOneEquiv P) (fixedSubmoduleOneEquiv P)
    ((fixedSubmoduleOneEquiv P).dualMap.trans P.toLinearMap.flip.toPerfPair.symm).symm

/-- The weight map of `oneEquiv P b` acts as the identity when coerced to `M`.

Not a `simp` lemma: `RootPairing.Equiv.toHom_one` and `RootPairing.Hom.weightMap_one` rewrite
`(1 : P.Aut).weightMap` to `LinearMap.id` inside the implicit `DFunLike.coe` codomain type on the
left-hand side, which triggers the `simpNF` linter. -/
theorem coe_oneEquiv_weightMap (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) (x : M) :
    ((oneEquiv P b).weightMap x : M) = x := by
  rw [oneEquiv, equivMap_weightMap, LinearEquiv.coe_coe, coe_fixedSubmoduleOneEquiv_apply]

@[simp]
theorem oneEquiv_indexEquiv (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) (i : ι) :
    (oneEquiv P b).indexEquiv i = P.foldedIndex 1 i := by
  rw [oneEquiv, equivMap_indexEquiv, foldedIndicesOneEquiv_apply]

@[simp]
theorem baseMap_oneEquiv (P : RootPairing ι R M N) [Finite ι]
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] (b : P.Base) :
    b.map (oneEquiv P b) = (one P b).base := by
  classical
  refine Base.ext (Finset.ext fun u ↦ ?_)
  rw [b.support_map_eq (oneEquiv P b), Finset.mem_image, (one P b).mem_support_base_iff]
  simp only [oneEquiv_indexEquiv, P.orbitSum_one]
  exact ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, by rw [← hju, P.coe_foldedIndex, P.orbitSum_one]⟩,
    fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext (by rw [P.coe_foldedIndex, P.orbitSum_one, hju])⟩⟩

/-- The canonical equivalence from `P` to any orbit-sum realization `F` of `1 : P.Aut` over a
characteristic-zero domain, acting as the identity on ambient weight vectors. -/
noncomputable def equivOne {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) : P.Equiv F.pairing :=
  Equiv.mk' P F.pairing (fixedSubmoduleOneEquiv P) (foldedIndicesOneEquiv P) fun i ↦
    Subtype.ext <| by
      rw [coe_fixedSubmoduleOneEquiv_apply, F.root_eq, foldedIndicesOneEquiv_apply,
        P.coe_foldedIndex, P.orbitSum_one]

/-- The weight map of `F.equivOne` acts as the identity when coerced to `M`.

Not a `simp` lemma: `RootPairing.Equiv.toHom_one` and `RootPairing.Hom.weightMap_one` rewrite
`(1 : P.Aut).weightMap` to `LinearMap.id` inside the implicit `DFunLike.coe` codomain type on the
left-hand side, which triggers the `simpNF` linter. -/
theorem coe_equivOne_weightMap {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) (x : M) :
    (F.equivOne.weightMap x : M) = x := by
  rw [equivOne, Equiv.mk'_weightMap, LinearEquiv.coe_coe, coe_fixedSubmoduleOneEquiv_apply]

@[simp]
theorem equivOne_indexEquiv {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) (i : ι) :
    F.equivOne.indexEquiv i = P.foldedIndex 1 i := by
  rw [equivOne, Equiv.mk'_indexEquiv, foldedIndicesOneEquiv_apply]

@[simp]
theorem baseMap_equivOne {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
    [P.IsRootSystem] {b : P.Base} (F : P.OrbitSumRealization b 1) :
    b.map F.equivOne = F.base := by
  classical
  refine Base.ext (Finset.ext fun u ↦ ?_)
  rw [b.support_map_eq F.equivOne, Finset.mem_image, F.mem_support_base_iff]
  refine ⟨fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, by simpa using congrArg Subtype.val hju⟩,
    fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext (by simpa using hju)⟩⟩

end OrbitSumRealization

end One

/-! ### Transport along intertwining equivalences -/

section Intertwining

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂} [Finite ι] [Finite ι₂]

/-- The bijection `P.foldedIndices σ ≃ P₂.foldedIndices τ` induced by an intertwining equivalence
`e : P.Equiv P₂`. -/
private noncomputable def foldedIndicesEquivOfIntertwining (e : P.Equiv P₂) {σ : P.Aut}
    {τ : P₂.Aut} (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    P.foldedIndices σ ≃ P₂.foldedIndices τ :=
  have hidx := e.toHom.indexEquiv_apply_of_weightMap (σ := σ.toHom) (τ := τ.toHom) he
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

@[simp]
private theorem coe_foldedIndicesEquivOfIntertwining_apply (e : P.Equiv P₂) {σ : P.Aut}
    {τ : P₂.Aut} (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (u : P.foldedIndices σ) :
    (foldedIndicesEquivOfIntertwining e he u : M₂) = e.weightMap (u : M) := by
  simp [foldedIndicesEquivOfIntertwining]

namespace OrbitSumRealization

/-- Shared characterization of the transported simple-root support under an intertwining based
equivalence `e : P.Equiv P₂`. -/
private theorem mem_image_foldedIndicesEquivOfIntertwining_iff
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    [DecidableEq (P₂.foldedIndices τ)]
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (v : P₂.foldedIndices τ) :
    v ∈ F.base.support.image (foldedIndicesEquivOfIntertwining e he) ↔
      ∃ k ∈ b₂.support, P₂.orbitSum τ k = (v : M₂) := by
  have hidx := e.toHom.indexEquiv_apply_of_weightMap (σ := σ.toHom) (τ := τ.toHom) he
  rw [Finset.mem_image]
  refine ⟨fun ⟨u, hu, huv⟩ ↦ ?_, fun ⟨k, hk, hkv⟩ ↦ ?_⟩
  · obtain ⟨j, hj, hju⟩ := (F.mem_support_base_iff u).mp hu
    refine ⟨e.indexEquiv j, (hbase j).mpr hj, ?_⟩
    rw [← P.weightMap_orbitSum e hidx j, hju, ← congrArg Subtype.val huv,
      coe_foldedIndicesEquivOfIntertwining_apply]
  · obtain ⟨j, rfl⟩ := e.indexEquiv.surjective k
    refine ⟨P.foldedIndex σ j, F.foldedIndex_mem_support_base ((hbase j).mp hk),
      Subtype.ext ?_⟩
    rw [coe_foldedIndicesEquivOfIntertwining_apply, P.coe_foldedIndex,
      P.weightMap_orbitSum e hidx j, hkv]

/-- Transport an orbit-sum realization along a based equivalence `e : P.Equiv P₂` intertwining `σ`
and `τ`. -/
noncomputable def map {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    P₂.OrbitSumRealization b₂ τ :=
  let eM := e.weightEquiv.fixedSubmoduleCongr (LinearMap.ext he)
  let eN := eM.symm.dualMap
  let eι := foldedIndicesEquivOfIntertwining e he
  let eqv := F.pairing.equivMap eι eM eN
  { pairing := F.pairing.map eι eM eN
    base := F.base.map eqv
    rootSystem := inferInstance
    reduced := eqv.isReduced
    crystallographic := eqv.toHom.isValuedIn ℤ
    evaluation := fun x y ↦ by simp [RootPairing.map, eN, eM]
    root_eq := fun v ↦ by
      obtain ⟨u, rfl⟩ := eι.surjective v
      simp [RootPairing.map, eM, eι]
    mem_support_base_iff := fun v ↦ by
      classical
      rw [F.base.support_map_eq eqv]
      simp only [eqv, equivMap_indexEquiv, eι]
      exact mem_image_foldedIndicesEquivOfIntertwining_iff F e hbase he v }

/-- The canonical equivalence from `F.pairing` to `(F.map e hbase he).pairing` over any commutative
ring, carrying each fixed vector and orbit-sum index to its image under `e.weightMap`. -/
noncomputable def mapEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.pairing.Equiv (F.map e hbase he).pairing :=
  F.pairing.equivMap (foldedIndicesEquivOfIntertwining e he)
    (e.weightEquiv.fixedSubmoduleCongr (LinearMap.ext he))
    (e.weightEquiv.fixedSubmoduleCongr (LinearMap.ext he)).symm.dualMap

@[simp]
theorem coe_mapEquiv_weightMap {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((F.mapEquiv e hbase he).weightMap x :
      LinearMap.fixedSubmodule τ.weightMap) : M₂) = e.weightMap (x : M) := by
  simp [mapEquiv, map]

@[simp]
theorem coe_mapEquiv_indexEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (u : P.foldedIndices σ) :
    (((F.mapEquiv e hbase he).indexEquiv u : P₂.foldedIndices τ) : M₂) =
      e.weightMap (u : M) := by
  simp [mapEquiv, map]

@[simp]
theorem baseMap_mapEquiv {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.base.map (F.mapEquiv e hbase he) = (F.map e hbase he).base := by
  classical
  refine Base.ext (Finset.ext fun v ↦ ?_)
  rw [F.base.support_map_eq (F.mapEquiv e hbase he), (F.map e hbase he).mem_support_base_iff]
  have heq : (F.mapEquiv e hbase he).indexEquiv = foldedIndicesEquivOfIntertwining e he := by
    ext u
    simp [mapEquiv, map]
  rw [heq]
  exact mem_image_foldedIndicesEquivOfIntertwining_iff F e hbase he v

/-- **Equivalence of realizations induced by an intertwining equivalence.** Over a
characteristic-zero domain, an equivalence `e : P.Equiv P₂` intertwining `σ` and `τ` induces an
equivalence `F.pairing.Equiv F₂.pairing` carrying each fixed vector and orbit-sum index to its
image under `e.weightMap`. -/
noncomputable def equivOfIntertwining [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.pairing.Equiv F₂.pairing :=
  Equiv.mk' F.pairing F₂.pairing
    (e.weightEquiv.fixedSubmoduleCongr (LinearMap.ext he))
    (foldedIndicesEquivOfIntertwining e he) fun u ↦ Subtype.ext (by simp)

@[simp]
theorem coe_equivOfIntertwining_weightMap [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((F.equivOfIntertwining F₂ e he).weightMap x :
      LinearMap.fixedSubmodule τ.weightMap) : M₂) = e.weightMap (x : M) := by
  simp [equivOfIntertwining]

@[simp]
theorem coe_equivOfIntertwining_indexEquiv [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x))
    (u : P.foldedIndices σ) :
    (((F.equivOfIntertwining F₂ e he).indexEquiv u : P₂.foldedIndices τ) : M₂) =
      e.weightMap (u : M) := by
  simp [equivOfIntertwining]

/-- When an intertwining equivalence `e : P.Equiv P₂` carries `b.support` to `b₂.support`, the
induced equivalence `F.equivOfIntertwining F₂ e he` carries `F.base` to `F₂.base`. -/
theorem baseMap_equivOfIntertwining [CharZero R] [IsDomain R]
    {b : P.Base} {b₂ : P₂.Base} {σ : P.Aut} {τ : P₂.Aut}
    (F : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ τ) (e : P.Equiv P₂)
    (hbase : ∀ j, e.indexEquiv j ∈ b₂.support ↔ j ∈ b.support)
    (he : ∀ x, e.weightMap (σ.weightMap x) = τ.weightMap (e.weightMap x)) :
    F.base.map (F.equivOfIntertwining F₂ e he) = F₂.base := by
  classical
  refine Base.ext (Finset.ext fun v ↦ ?_)
  rw [F.base.support_map_eq (F.equivOfIntertwining F₂ e he), F₂.mem_support_base_iff]
  have heq :
      (F.equivOfIntertwining F₂ e he).indexEquiv = foldedIndicesEquivOfIntertwining e he := by
    ext u
    simp [equivOfIntertwining]
  rw [heq]
  exact mem_image_foldedIndicesEquivOfIntertwining_iff F e hbase he v

end OrbitSumRealization

end Intertwining

end RootPairing
