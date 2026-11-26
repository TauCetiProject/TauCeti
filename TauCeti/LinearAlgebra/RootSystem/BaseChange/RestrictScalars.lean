/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Dominance
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Basic
public import TauCeti.LinearAlgebra.RootSystem.RootSpanProj
import TauCeti.Algebra.Group.Submonoid.Closure

/-!
# Bases, automorphisms and chambers of a restriction of scalars

Let `P` be a root pairing over a field `L` whose pairings lie in a subfield `K`. Mathlib's
`RootPairing.restrictScalars'` is the root system `P.restrictScalars' K` on the `K`-spans of the
roots and of the coroots, with the same root indices, roots, coroots and pairings. For `K = L` it
is the restriction of `P` to the span of its roots, a root system even when the roots of `P` do not
span: the ambient weight space splits off a central part on which every coroot vanishes.

This file transports the combinatorial structure of `P` to `P.restrictScalars' K`, so that
statements about root systems apply to root pairings whose roots need not span. The restriction is
reduced or crystallographic when `P` is. A base of `P` is a base of the restriction with the same
support, the same heights and the same Cartan matrix, and its positive monoid is the positive
monoid of `P` read on the span. An equivalence of root pairings restricts to an equivalence of the
restrictions with the same root bijection, so an automorphism permuting the simple roots restricts
to one with the same property, and it has the same root orbits and orbit sums. Integral root
dominance on the `K`-span of the roots is that of `P`, and for `K = L` over an ordered field so is
the dominant chamber.

The projection `RootPairing.rootSpanProj` onto the span of the roots along the common kernel of the
coroot functionals commutes with restricted equivalences of root pairings. It moves a weight of `P`
into the restriction without changing its dominance, which reduces statements about dominant
weights of an arbitrary root pairing to statements about root systems.

## Main definitions

* `RootPairing.Base.restrictScalars'`: the base of `P.restrictScalars' K` with the simple roots of
  a base of `P`.
* `RootPairing.Equiv.restrictScalars'`: the equivalence of restrictions of scalars induced by an
  equivalence of root pairings.

## Main results

* `RootPairing.algebraMap_coroot'_restrictScalars'`: the coroot functionals of the restriction are
  those of `P`.
* `RootPairing.isReduced_restrictScalars'`, `RootPairing.isValuedIn_restrictScalars'`: the
  restriction is reduced, and valued in every ring in which `P` is valued.
* `RootPairing.Base.height_restrictScalars'`, `RootPairing.Base.cartanMatrix_restrictScalars'`:
  the restricted base has the heights and the Cartan matrix of the original one.
* `RootPairing.mem_posRootCone_restrictScalars'_iff`: the positive monoid of the restricted base
  consists of the vectors of the span lying in the positive monoid of `P`.
* `RootPairing.coe_orbitSum_restrictScalars'`: the orbit sums of a restricted automorphism are
  those of the original one.
* `RootPairing.rootLE_restrictScalars'_iff`: integral root dominance on the `K`-span of the roots
  agrees with that of `P`.
* `RootPairing.mem_dominantChamber_restrictScalars'_iff`: for `K = L`, dominance on the span of the
  roots agrees with that of `P`.
* `RootPairing.Equiv.weightMap_restrictScalars'_rootSpanProj`,
  `RootPairing.rootSpanProj_mem_dominantChamber_iff`: the projection onto the span of the roots is
  equivariant and preserves dominance.
-/

public section

open Function Set
open Submodule (span)

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N) (K : Type*) [Field K] [Algebra K L] [Module K M] [Module K N]
  [IsScalarTower K L M] [IsScalarTower K L N] [P.IsBalanced] [P.IsValuedIn K]

/-! ### Coroot values, pairings and reducedness -/

/-- The coroot functionals of `P.restrictScalars' K` are those of `P`, read on the `K`-span of the
roots. -/
theorem algebraMap_coroot'_restrictScalars' (i : ι) (x : span K (range P.root)) :
    algebraMap K L ((P.restrictScalars' K).coroot' i x) = P.coroot' i x := by
  simp [coroot', restrictScalars_toLinearMap_apply_apply]

/-- The restriction of scalars of a reduced root pairing is reduced. -/
instance isReduced_restrictScalars' [P.IsReduced] : (P.restrictScalars' K).IsReduced where
  eq_or_eq_neg i j hij := by
    have hL : ¬ LinearIndependent L ![P.root i, P.root j] := fun h ↦ hij <| by
      refine LinearIndependent.of_comp (span K (range P.root)).subtype ?_
      convert h.restrict_scalars' K using 1
      ext k
      fin_cases k <;> simp
    exact (IsReduced.eq_or_eq_neg i j hL).imp (fun h ↦ Subtype.ext (by simpa using h))
      fun h ↦ Subtype.ext (by simpa using h)

/-- The restriction of scalars of a root pairing valued in `S` is valued in `S`; in particular the
restriction of scalars of a crystallographic root pairing is crystallographic. -/
instance isValuedIn_restrictScalars' (S : Type*) [CommRing S] [Algebra S K] [Algebra S L]
    [IsScalarTower S K L] [P.IsValuedIn S] : (P.restrictScalars' K).IsValuedIn S where
  exists_value i j := by
    obtain ⟨s, hs⟩ := IsValuedIn.exists_value (P := P) (S := S) i j
    refine ⟨s, FaithfulSMul.algebraMap_injective K L ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hs, restrictScalars_pairing]

/-- The `S`-valued pairings of the restriction of scalars are those of `P`. -/
@[simp]
theorem pairingIn_restrictScalars' (S : Type*) [CommRing S] [Algebra S K] [Algebra S L]
    [IsScalarTower S K L] [FaithfulSMul S L] [P.IsValuedIn S] (i j : ι) :
    (P.restrictScalars' K).pairingIn S i j = P.pairingIn S i j :=
  FaithfulSMul.algebraMap_injective S L <| by
    rw [algebraMap_pairingIn, IsScalarTower.algebraMap_apply S K L, algebraMap_pairingIn,
      restrictScalars_pairing]

/-! ### Additive closures of roots and coroots -/

variable {P K}

/-- A vector of the `K`-span of the roots is a sum of roots of `P.restrictScalars' K` indexed by `s`
exactly when it is a sum of the corresponding roots of `P`. -/
theorem mem_closure_root_restrictScalars'_iff {s : Set ι} {x : span K (range P.root)} :
    x ∈ AddSubmonoid.closure ((P.restrictScalars' K).root '' s) ↔
      (x : M) ∈ AddSubmonoid.closure (P.root '' s) :=
  AddSubmonoid.mem_closure_image_iff_coe (P.restrictScalars_coe_root K)

/-- A vector of the `K`-span of the coroots is a sum of coroots of `P.restrictScalars' K` indexed by
`s` exactly when it is a sum of the corresponding coroots of `P`. -/
theorem mem_closure_coroot_restrictScalars'_iff {s : Set ι} {y : span K (range P.coroot)} :
    y ∈ AddSubmonoid.closure ((P.restrictScalars' K).coroot '' s) ↔
      (y : N) ∈ AddSubmonoid.closure (P.coroot '' s) :=
  AddSubmonoid.mem_closure_image_iff_coe (P.restrictScalars_coe_coroot K)

/-! ### The restricted base -/

namespace Base

variable (b : P.Base) (K)

/-- The **base of the restriction of scalars** `P.restrictScalars' K` given by a base `b` of `P`:
its simple roots are those of `b`. -/
def restrictScalars' : (P.restrictScalars' K).Base where
  support := b.support
  linearIndepOn_root := by
    refine .of_comp (span K (range P.root)).subtype ?_
    rw [show (span K (range P.root)).subtype ∘ (P.restrictScalars' K).root = P.root from
      funext (P.restrictScalars_coe_root K)]
    exact b.linearIndepOn_root.linearIndependent.restrict_scalars' K
  linearIndepOn_coroot := by
    refine .of_comp (span K (range P.coroot)).subtype ?_
    rw [show (span K (range P.coroot)).subtype ∘ (P.restrictScalars' K).coroot = P.coroot from
      funext (P.restrictScalars_coe_coroot K)]
    exact b.linearIndepOn_coroot.linearIndependent.restrict_scalars' K
  root_mem_or_neg_mem i := by
    refine (b.root_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact mem_closure_root_restrictScalars'_iff.mpr h
  coroot_mem_or_neg_mem i := by
    refine (b.coroot_mem_or_neg_mem i).imp (fun h ↦ ?_) fun h ↦ ?_ <;>
      exact mem_closure_coroot_restrictScalars'_iff.mpr h

/-- The simple roots of the restricted base are those of `b`. -/
@[simp]
theorem support_restrictScalars' : (b.restrictScalars' K).support = b.support := (rfl)

/-- The `S`-valued Cartan matrix of the restricted base is that of `b`. -/
@[simp]
theorem cartanMatrixIn_restrictScalars' (S : Type*) [CommRing S] [Algebra S K] [Algebra S L]
    [IsScalarTower S K L] [FaithfulSMul S L] [P.IsValuedIn S]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrixIn S i j =
      b.cartanMatrixIn S ⟨i, by simpa using i.property⟩ ⟨j, by simpa using j.property⟩ := by
  simp [cartanMatrixIn_def]

/-- The Cartan matrix of the restricted base is that of `b`. -/
theorem cartanMatrix_restrictScalars' [CharZero L] [P.IsCrystallographic]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrix i j =
      b.cartanMatrix ⟨i, by simpa using i.property⟩ ⟨j, by simpa using j.property⟩ :=
  b.cartanMatrixIn_restrictScalars' K ℤ i j

/-- The heights of the roots relative to the restricted base are their heights relative to `b`. -/
@[simp]
theorem height_restrictScalars' [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).height i = b.height i := by
  obtain ⟨f, -, -, hf⟩ := (b.restrictScalars' K).exists_root_eq_sum_int i
  rw [height_eq_sum hf, support_restrictScalars', b.height_eq_sum (f := f)]
  simpa using congrArg Subtype.val hf

/-- A root is positive for the restricted base exactly when it is positive for `b`. -/
@[simp]
theorem isPos_restrictScalars'_iff [CharZero K] [CharZero L] (i : ι) :
    (b.restrictScalars' K).IsPos i ↔ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_restrictScalars']

end Base

variable (K) in
/-- **The positive monoid of the restricted base**: a vector of the `K`-span of the roots is a
natural sum of simple roots of `b.restrictScalars' K` exactly when it is a natural sum of simple
roots of `b`. -/
@[simp]
theorem mem_posRootCone_restrictScalars'_iff (b : P.Base) {x : span K (range P.root)} :
    x ∈ TauCeti.posRootCone (P.restrictScalars' K) (b.restrictScalars' K) ↔
      (x : M) ∈ TauCeti.posRootCone P b := by
  simp only [TauCeti.mem_posRootCone, Subtype.ext_iff, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, restrictScalars_coe_root, Base.support_restrictScalars']

variable (K) in
/-- **Integral root dominance on the restriction**: two vectors of the `K`-span of the roots compare
for `b.restrictScalars' K` exactly when they compare for `b`. -/
@[simp]
theorem rootLE_restrictScalars'_iff (b : P.Base) {x y : span K (range P.root)} :
    (P.restrictScalars' K).rootLE (b.restrictScalars' K) x y ↔ P.rootLE b x y := by
  simp [rootLE_iff_sub_mem_posRootCone]

/-! ### Restricting equivalences -/

namespace Equiv

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂] [Module L M₂] [Module L N₂]
  [Module K M₂] [Module K N₂] [IsScalarTower K L M₂] [IsScalarTower K L N₂]
  {Q : RootPairing ι₂ L M₂ N₂} [Q.IsBalanced] [Q.IsValuedIn K] (e : P.Equiv Q)

omit [Module K N] [IsScalarTower K L N] [P.IsBalanced] [P.IsValuedIn K] [Module K N₂]
  [IsScalarTower K L N₂] [Q.IsBalanced] [Q.IsValuedIn K] in
/-- An equivalence of root pairings carries the `K`-span of the roots onto the `K`-span of the
roots. -/
theorem map_span_root :
    (span K (range P.root)).map (e.weightEquiv.restrictScalars K : M →ₗ[K] M₂) =
      span K (range Q.root) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (e.weightEquiv.restrictScalars K : M →ₗ[K] M₂) ∘ P.root = Q.root ∘ e.indexEquiv :=
    funext fun i ↦ by simp [Hom.root_weightMap_apply]
  rw [h, EquivLike.range_comp]

omit [Module K M] [IsScalarTower K L M] [P.IsBalanced] [P.IsValuedIn K] [Module K M₂]
  [IsScalarTower K L M₂] [Q.IsBalanced] [Q.IsValuedIn K] in
/-- An equivalence of root pairings carries the `K`-span of the coroots of its target onto the
`K`-span of the coroots of its source. -/
theorem map_span_coroot :
    (span K (range Q.coroot)).map (e.coweightEquiv.restrictScalars K : N₂ →ₗ[K] N) =
      span K (range P.coroot) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (e.coweightEquiv.restrictScalars K : N₂ →ₗ[K] N) ∘ Q.coroot =
      P.coroot ∘ e.indexEquiv.symm :=
    funext fun i ↦ by simp [Hom.coroot_coweightMap_apply]
  rw [h, EquivLike.range_comp]

variable (K) in
/-- The **restriction of an equivalence of root pairings** to the `K`-spans of the roots and of the
coroots: an equivalence from `P.restrictScalars' K` to `Q.restrictScalars' K` with the same root
bijection. -/
noncomputable def restrictScalars' : (P.restrictScalars' K).Equiv (Q.restrictScalars' K) where
  weightMap := ((e.weightEquiv.restrictScalars K).ofSubmodules _ _ e.map_span_root).toLinearMap
  coweightMap :=
    ((e.coweightEquiv.restrictScalars K).ofSubmodules _ _ e.map_span_coroot).toLinearMap
  indexEquiv := e.indexEquiv
  weight_coweight_transpose := by
    refine LinearMap.ext fun y ↦ LinearMap.ext fun x ↦ FaithfulSMul.algebraMap_injective K L ?_
    simpa [restrictScalars_toLinearMap_apply_apply] using e.toLinearMap_weightEquiv x y
  root_weightMap := funext fun i ↦ Subtype.ext <| by simp [Hom.root_weightMap_apply]
  coroot_coweightMap := funext fun i ↦ Subtype.ext <| by simp [Hom.coroot_coweightMap_apply]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

/-- The weight map of the restricted equivalence is the weight map of `e`. -/
@[simp]
theorem coe_weightMap_restrictScalars'_apply (x : span K (range P.root)) :
    ((e.restrictScalars' K).weightMap x : M₂) = e.weightMap x := by
  simp [restrictScalars']

/-- The coweight map of the restricted equivalence is the coweight map of `e`. -/
@[simp]
theorem coe_coweightMap_restrictScalars'_apply (y : span K (range Q.coroot)) :
    ((e.restrictScalars' K).coweightMap y : N) = e.coweightMap y := by
  simp [restrictScalars']

/-- The root bijection of the restricted equivalence is that of `e`. -/
@[simp]
theorem indexEquiv_restrictScalars' : (e.restrictScalars' K).indexEquiv = e.indexEquiv := (rfl)

end Equiv

/-! ### Orbit sums of a restricted automorphism -/

section OrbitSum

variable [Finite ι] (σ : P.Aut) (i : ι)

/-- The root orbits of the restriction of an automorphism are those of the automorphism. -/
@[simp]
theorem orbitIndices_restrictScalars' :
    (P.restrictScalars' K).orbitIndices (σ.restrictScalars' K) i = P.orbitIndices σ i := by
  ext j
  simp

/-- **The orbit sums of a restricted automorphism are the original orbit sums.** -/
@[simp]
theorem coe_orbitSum_restrictScalars' :
    ((P.restrictScalars' K).orbitSum (σ.restrictScalars' K) i : M) = P.orbitSum σ i := by
  simp [orbitSum_def]

end OrbitSum

/-! ### The projection onto the span of the roots -/

section RootSpanRestriction

variable {P : RootPairing ι L M N} [P.IsBalanced]

/-- On the span of the roots, the coroot functionals of `P.restrictScalars' L` are those of `P`. -/
theorem coroot'_restrictScalars'_self (i : ι) (x : span L (range P.root)) :
    (P.restrictScalars' L).coroot' i x = P.coroot' i x := by
  simpa using P.algebraMap_coroot'_restrictScalars' L i x

/-- **The projection onto the span of the roots is equivariant**: the restriction of an equivalence
of root pairings to the spans of the roots intertwines the two projections. -/
theorem Equiv.weightMap_restrictScalars'_rootSpanProj {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂]
    [AddCommGroup N₂] [Module L M₂] [Module L N₂] {Q : RootPairing ι₂ L M₂ N₂} [Q.IsBalanced]
    (e : P.Equiv Q) (x : M) :
    (e.restrictScalars' L).weightMap (P.rootSpanProj x) = Q.rootSpanProj (e.weightMap x) := by
  set y := (e.restrictScalars' L).weightMap (P.rootSpanProj x)
  have hz : e.weightMap (x - P.rootSpanProj x) ∈ LinearMap.ker Q.rootSpanProj := by
    rw [ker_rootSpanProj, Submodule.mem_iInf]
    intro j
    have h := Submodule.mem_iInf _ |>.mp (P.sub_rootSpanProj_mem x) (e.indexEquiv.symm j)
    rw [LinearMap.mem_ker] at h ⊢
    simpa [h] using e.coroot'_weightEquiv (e.indexEquiv.symm j) (x - P.rootSpanProj x)
  have hx : e.weightMap x = y + e.weightMap (x - P.rootSpanProj x) := by
    simp [y, map_sub]
  rw [hx, map_add, LinearMap.mem_ker.mp hz, add_zero, rootSpanProj_apply_of_mem y.property]

end RootSpanRestriction

/-! ### Dominance on the span of the roots -/

section Order

variable {P : RootPairing ι L M N} [P.IsBalanced] [Preorder L] (b : P.Base)

/-- **The dominant chamber of the root-span restriction**: a vector of the span of the roots is
dominant for `b.restrictScalars' L` exactly when it is dominant for `b`. -/
theorem mem_dominantChamber_restrictScalars'_iff {x : span L (range P.root)} :
    x ∈ dominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      (x : M) ∈ dominantChamber P b := by
  simp only [mem_dominantChamber, coroot'_restrictScalars'_self, Base.support_restrictScalars']

/-- The projection of a vector onto the span of the roots is dominant for `b.restrictScalars' L`
exactly when the vector is dominant for `b`. -/
theorem rootSpanProj_mem_dominantChamber_iff {x : M} :
    P.rootSpanProj x ∈ dominantChamber (P.restrictScalars' L) (b.restrictScalars' L) ↔
      x ∈ dominantChamber P b := by
  rw [mem_dominantChamber_restrictScalars'_iff]
  simp only [mem_dominantChamber, coroot'_rootSpanProj]

end Order

end RootPairing
