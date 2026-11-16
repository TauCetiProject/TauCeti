/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.OrbitSum
import Mathlib.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Realizations of folded root systems on the fixed subspace

Let `P` be a finite root pairing with base `b` and automorphism `σ`. The distinct orbit sums of the
roots of `P` under `σ` form the finite set `RootPairing.foldedIndices P σ` inside the fixed
submodule `LinearMap.fixedSubmodule σ.weightMap`.

An **orbit-sum realization** (`RootPairing.OrbitSumRealization P b σ`) packages a reduced
crystallographic root system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual whose
roots are indexed by `P.foldedIndices σ` via the ambient inclusion, whose pairing is evaluation,
and whose base consists of the orbit sums of the simple roots of `b`.

Over a characteristic-zero integral domain, an orbit-sum realization is unique: the evaluation
pairing and the root vectors determine the coroots and reflections via
`RootPairing.IsRootSystem.ext`, and the simple-support equation determines the base via
`RootPairing.Base.ext`. For any based automorphism `σ`, positivity in any realization agrees with
having a positive original-root lift. For the identity automorphism, the original based root system
itself supplies a realization (including in rank zero), and any based equivalence intertwining two
automorphisms transports realizations and induces a canonical based equivalence between them.

## Main definitions

* `RootPairing.OrbitSumRealization`: a reduced crystallographic based root system on the fixed
  submodule of `σ` and its linear dual whose roots are `P.foldedIndices σ` and whose simple roots
  are the simple-orbit sums of `b`.
* `RootPairing.OrbitSumRealization.ofId`: the canonical realization for the identity automorphism.
* `RootPairing.OrbitSumRealization.equivOfId`: the canonical based equivalence identifying `P` with
  any realization for the identity automorphism.
* `RootPairing.OrbitSumRealization.map`: transport of an orbit-sum realization along a based
  equivalence intertwining two automorphisms.
* `RootPairing.OrbitSumRealization.equivOfEquiv`: the canonical based equivalence between two
  realizations induced by an intertwining based equivalence.

## Main results

* `RootPairing.OrbitSumRealization.instSubsingleton`: over a characteristic-zero domain, an
  orbit-sum realization is unique.
* `RootPairing.OrbitSumRealization.isPos_iff` and
  `RootPairing.OrbitSumRealization.isPos_orbitSum_iff`: for a based automorphism, the positive
  folded roots are precisely the orbit sums of positive original roots.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008.
-/

public section

namespace RootPairing

open TauCeti

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An **orbit-sum realization** of the folding of `(P, b)` by `σ`: a reduced crystallographic root
system on the fixed submodule `LinearMap.fixedSubmodule σ.weightMap` and its linear dual, indexed
by the distinct orbit sums `P.foldedIndices σ`, with pairing given by evaluation, roots given by
the ambient orbit-sum vectors, and base supported on the simple-orbit sums. -/
structure OrbitSumRealization (P : RootPairing ι R M N) [Finite ι]
    (b : P.Base) (σ : P.Aut) where
  /-- The folded root pairing on the fixed submodule and its linear dual. -/
  pairing : RootPairing (P.foldedIndices σ) R (LinearMap.fixedSubmodule σ.weightMap)
    (Module.Dual R (LinearMap.fixedSubmodule σ.weightMap))
  /-- The base of the folded root pairing. -/
  base : pairing.Base
  /-- Both folded roots and folded coroots span. -/
  rootSystem : pairing.IsRootSystem
  /-- The folded root system is reduced. -/
  reduced : pairing.IsReduced
  /-- The folded root system is crystallographic. -/
  crystallographic : pairing.IsCrystallographic
  /-- The perfect pairing is evaluation of linear functionals on fixed vectors. -/
  evaluation : ∀ x y, pairing.toLinearMap x y = y x
  /-- Each folded root has the index's ambient vector as its underlying element of `M`. -/
  root_eq : ∀ i, (pairing.root i : M) = (i : M)
  /-- The simple folded roots are precisely the orbit sums of the simple roots of `b`. -/
  base_eq : ∀ i, i ∈ base.support ↔ ∃ j ∈ b.support, P.orbitSum σ j = (i : M)

namespace OrbitSumRealization

section Basic

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

instance instIsRootSystem (F : P.OrbitSumRealization b σ) : F.pairing.IsRootSystem :=
  F.rootSystem

instance instIsReduced (F : P.OrbitSumRealization b σ) : F.pairing.IsReduced :=
  F.reduced

instance instIsCrystallographic (F : P.OrbitSumRealization b σ) : F.pairing.IsCrystallographic :=
  F.crystallographic

@[simp]
theorem evaluation_apply (F : P.OrbitSumRealization b σ)
    (x : LinearMap.fixedSubmodule σ.weightMap)
    (y : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap)) :
    F.pairing.toLinearMap x y = y x :=
  F.evaluation x y

theorem coroot'_apply (F : P.OrbitSumRealization b σ) (i : P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' i x = F.pairing.coroot i x :=
  F.evaluation x (F.pairing.coroot i)

/-- The bilinear pairing of an orbit-sum realization is canonical evaluation on the fixed
submodule and its dual. -/
theorem toLinearMap_eq (F : P.OrbitSumRealization b σ) :
    F.pairing.toLinearMap = Module.Dual.eval R (LinearMap.fixedSubmodule σ.weightMap) := by
  ext x y
  exact F.evaluation x y

@[simp]
theorem coe_root (F : P.OrbitSumRealization b σ) (i : P.foldedIndices σ) :
    (F.pairing.root i : M) = (i : M) :=
  F.root_eq i

theorem mem_base_support_iff (F : P.OrbitSumRealization b σ) (i : P.foldedIndices σ) :
    i ∈ F.base.support ↔ ∃ j ∈ b.support, P.orbitSum σ j = (i : M) :=
  F.base_eq i

/-- The orbit sum of any simple root of `b` lies in the simple support of any realization. -/
theorem orbitSum_mem_base_support (F : P.OrbitSumRealization b σ) {j : ι} (hj : j ∈ b.support) :
    (⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩ : P.foldedIndices σ) ∈ F.base.support :=
  (F.base_eq _).mpr ⟨j, hj, rfl⟩

end Basic

/-! ### Uniqueness -/

section Uniqueness

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} [IsDomain R] [CharZero R]

/-- **Uniqueness of the folded root pairing**: any two orbit-sum realizations of `(P, b, σ)` have
identical root pairings, and in particular identical coroots and reflections. -/
theorem pairing_eq (F₁ F₂ : P.OrbitSumRealization b σ) : F₁.pairing = F₂.pairing := by
  refine RootPairing.IsRootSystem.ext (F₁.toLinearMap_eq.trans F₂.toLinearMap_eq.symm) ?_
  ext i
  exact (F₁.root_eq i).trans (F₂.root_eq i).symm

/-- **Uniqueness of an orbit-sum realization**: over a characteristic-zero domain, the root-vector,
evaluation, and simple-support equations determine the entire realization uniquely. -/
instance instSubsingleton : Subsingleton (P.OrbitSumRealization b σ) where
  allEq F₁ F₂ := by
    have hp : F₁.pairing = F₂.pairing := pairing_eq F₁ F₂
    cases F₁ with
    | mk _ _ _ _ _ _ _ bs₁ =>
      cases F₂ with
      | mk _ _ _ _ _ _ _ bs₂ =>
        dsimp only at hp; subst hp
        congr 1
        exact RootPairing.Base.ext (Finset.ext fun i ↦ by rw [bs₁, bs₂])

end Uniqueness

/-! ### Positivity -/

section Positivity

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut} [CharZero R]

/-- The ambient inclusion carries the positive root cone of any orbit-sum realization into the
positive root cone of `b`. -/
theorem coe_mem_posRootCone_of_mem_posRootCone (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap}
    (hx : x ∈ posRootCone F.pairing F.base) : (x : M) ∈ posRootCone P b := by
  obtain ⟨f, rfl⟩ := (mem_posRootCone F.pairing F.base).mp hx
  rw [Submodule.coe_sum]
  refine sum_mem fun s hs ↦ ?_
  rw [AddSubmonoidClass.coe_nsmul, F.root_eq s]
  obtain ⟨j, hj, hjs⟩ := (F.base_eq s).mp hs
  rw [← hjs]
  exact nsmul_mem (P.orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hj)) _

private theorem not_mem_posRootCone_of_not_isPos
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) {i : ι} (hi : ¬ b.IsPos i)
    (hmem : P.orbitSum σ i ∈ posRootCone P b) : False := by
  have hpos' : b.IsPos (P.reflectionPerm i i) :=
    (isPos_reflectionPerm_self_iff_mem_negRoots P b i).mpr ((mem_negRoots P b i).mpr hi)
  have hneg : -P.orbitSum σ i ∈ posRootCone P b := by
    rw [← P.orbitSum_reflectionPerm_self σ i]
    exact P.orbitSum_mem_posRootCone hσ hpos'
  exact P.orbitSum_ne_zero hσ i
    (eq_zero_of_add_eq_zero_of_mem_posRootCone P b hmem hneg (add_neg_cancel _))

/-- **Positivity in an orbit-sum realization**: for a based automorphism `σ`, a folded root is
positive in the realization exactly when it is the orbit sum of a positive original root. -/
theorem isPos_iff (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (x : P.foldedIndices σ) :
    F.base.IsPos x ↔ ∃ i : ι, b.IsPos i ∧ P.orbitSum σ i = (x : M) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp x.2
    by_cases hpos : b.IsPos i
    · exact ⟨i, hpos, hi⟩
    · refine False.elim (not_mem_posRootCone_of_not_isPos hσ hpos ?_)
      rw [hi, ← F.root_eq x]
      exact F.coe_mem_posRootCone_of_mem_posRootCone hσ
        (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr hx))
  · rintro ⟨i, hi, hix⟩
    by_contra hneg
    have hmem₁ : (x : M) ∈ posRootCone P b := hix ▸ P.orbitSum_mem_posRootCone hσ hi
    have hmem₂ : -(x : M) ∈ posRootCone P b := by
      have hpos' : F.base.IsPos (F.pairing.reflectionPerm x x) :=
        (isPos_reflectionPerm_self_iff_mem_negRoots F.pairing F.base x).mpr
          ((mem_negRoots F.pairing F.base x).mpr hneg)
      have hcoe := F.coe_mem_posRootCone_of_mem_posRootCone hσ
        (root_mem_posRootCone_of_mem_posRoots F.pairing F.base ((mem_posRoots _ _ _).mpr hpos'))
      rwa [root_reflectionPerm, reflection_apply_self, Submodule.coe_neg, F.root_eq] at hcoe
    exact P.orbitSum_ne_zero hσ i
      (hix.trans (eq_zero_of_add_eq_zero_of_mem_posRootCone P b hmem₁ hmem₂ (add_neg_cancel _)))

/-- An orbit sum is a positive folded root exactly when the lifting original root is positive. -/
theorem isPos_orbitSum_iff (F : P.OrbitSumRealization b σ)
    (hσ : ∀ j ∈ b.support, σ.indexEquiv j ∈ b.support) (i : ι) :
    F.base.IsPos ⟨P.orbitSum σ i, P.orbitSum_mem_foldedIndices σ i⟩ ↔ b.IsPos i := by
  rw [F.isPos_iff hσ]
  refine ⟨fun ⟨j, hj, hij⟩ ↦ ?_, fun hi ↦ ⟨i, hi, rfl⟩⟩
  dsimp only at hij
  by_contra hi
  exact not_mem_posRootCone_of_not_isPos hσ hi (hij ▸ P.orbitSum_mem_posRootCone hσ hj)

end Positivity

/-! ### Helper for transporting pairings along equivalences -/

section MapHelpers

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]

/-- The canonical root-pairing equivalence from `P` to `P.map e f g`. -/
private def equivMap (P : RootPairing ι R M N) (e : ι ≃ ι₂) (f : M ≃ₗ[R] M₂) (g : N ≃ₗ[R] N₂) :
    P.Equiv (P.map e f g) where
  weightMap := f.toLinearMap
  coweightMap := g.symm.toLinearMap
  indexEquiv := e
  weight_coweight_transpose := by
    ext x y
    simp [RootPairing.map]
  root_weightMap := by
    ext i
    simp [RootPairing.map]
  coroot_coweightMap := by
    ext i
    simp [RootPairing.map]
  bijective_weightMap := f.bijective
  bijective_coweightMap := g.symm.bijective

private theorem isReduced_of_equiv {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
    (E : P.Equiv Q) [P.IsReduced] : Q.IsReduced where
  eq_or_eq_neg i j hdep := by
    obtain ⟨i, rfl⟩ := E.indexEquiv.surjective i
    obtain ⟨j, rfl⟩ := E.indexEquiv.surjective j
    have hdep' : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦
      hdep ((E.toHom.linearIndependent_root_indexEquiv_iff E.bijective_weightMap.injective i j).mpr
        hli)
    rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply]
    rcases IsReduced.eq_or_eq_neg i j hdep' with h | h
    · exact Or.inl (congrArg E.weightMap h)
    · exact Or.inr (by rw [h, map_neg])

end MapHelpers

/-! ### The identity automorphism -/

section Id

/-- The linear equivalence identifying `M` with the fixed submodule of the identity automorphism. -/
private def fixedSubmoduleOneEquiv (P : RootPairing ι R M N) :
    M ≃ₗ[R] LinearMap.fixedSubmodule (1 : P.Aut).weightMap where
  toFun x := ⟨x, LinearMap.mem_fixedSubmodule_iff.mpr rfl⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def ofIdIndexEquiv (P : RootPairing ι R M N) [Finite ι] :
    ι ≃ P.foldedIndices 1 :=
  _root_.Equiv.ofBijective
    (fun i ↦ ⟨P.root i, mem_foldedIndices.mpr ⟨i, P.orbitSum_one i⟩⟩)
    ⟨fun _ _ h ↦ P.root.injective (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨i, hi⟩ := mem_foldedIndices.mp x.2
      exact ⟨i, Subtype.ext ((P.orbitSum_one i).symm.trans hi)⟩⟩

private theorem coe_ofIdIndexEquiv (P : RootPairing ι R M N) [Finite ι] (j : ι) :
    ((ofIdIndexEquiv P j : P.foldedIndices 1) : M) = P.root j :=
  rfl

private noncomputable def ofIdCoweightEquiv (P : RootPairing ι R M N) :
    N ≃ₗ[R] Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap) :=
  P.flip.toPerfPair.trans (fixedSubmoduleOneEquiv P).symm.dualMap

private noncomputable def ofIdPairing (P : RootPairing ι R M N) [Finite ι] :
    RootPairing (P.foldedIndices 1) R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)
      (Module.Dual R (LinearMap.fixedSubmodule (1 : P.Aut).weightMap)) :=
  P.map (ofIdIndexEquiv P) (fixedSubmoduleOneEquiv P) (ofIdCoweightEquiv P)

private noncomputable def ofIdPairingEquiv (P : RootPairing ι R M N) [Finite ι] :
    P.Equiv (ofIdPairing P) :=
  equivMap P (ofIdIndexEquiv P) (fixedSubmoduleOneEquiv P) (ofIdCoweightEquiv P)

/-- **The orbit-sum realization for the identity automorphism**: transporting `(P, b)` onto the
fixed submodule of `1` (which is all of `M`) and its linear dual recovers the original based root
system, including in rank zero. -/
noncomputable def ofId (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem] [P.IsReduced]
    [P.IsCrystallographic] (b : P.Base) : P.OrbitSumRealization b 1 where
  pairing := ofIdPairing P
  base := b.map (ofIdPairingEquiv P)
  rootSystem := inferInstanceAs ((P.map _ _ _).IsRootSystem)
  reduced := isReduced_of_equiv (ofIdPairingEquiv P)
  crystallographic := (ofIdPairingEquiv P).toHom.isValuedIn ℤ
  evaluation x y := by
    have h1 : (ofIdPairing P).toLinearMap x y =
        (ofIdCoweightEquiv P) ((ofIdCoweightEquiv P).symm y) x := rfl
    rw [h1, LinearEquiv.apply_symm_apply]
  root_eq i := by
    obtain ⟨j, rfl⟩ := (ofIdIndexEquiv P).surjective i
    rw [coe_ofIdIndexEquiv]
    exact congrArg Subtype.val
      (Hom.root_weightMap_apply P (ofIdPairing P) j (ofIdPairingEquiv P).toHom).symm
  base_eq i := by
    classical
    rw [b.support_map_eq, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, by simp [ofIdPairingEquiv, equivMap, coe_ofIdIndexEquiv]⟩
    · rintro ⟨j, hj, hji⟩
      refine ⟨j, hj, Subtype.ext ?_⟩
      simpa [ofIdPairingEquiv, equivMap, coe_ofIdIndexEquiv] using hji

variable {P : RootPairing ι R M N} [Finite ι] {b : P.Base} [IsDomain R] [CharZero R]
  [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]

/-- **Canonical identification for the identity automorphism**: any orbit-sum realization for `1` is
canonically equivalent to `(P, b)` by the ambient inclusion on weights. -/
noncomputable def equivOfId (F : P.OrbitSumRealization b 1) : P.Equiv F.pairing :=
  (Subsingleton.elim (ofId P b) F) ▸ ofIdPairingEquiv P

theorem coe_equivOfId_weightMap (F : P.OrbitSumRealization b 1) (x : M) :
    ((F.equivOfId.weightMap x : LinearMap.fixedSubmodule (1 : P.Aut).weightMap) : M) = x := by
  obtain rfl : F = ofId P b := Subsingleton.elim _ _
  rfl

@[simp]
theorem coe_equivOfId_indexEquiv (F : P.OrbitSumRealization b 1) (i : ι) :
    ((F.equivOfId.indexEquiv i : P.foldedIndices 1) : M) = P.root i := by
  obtain rfl : F = ofId P b := Subsingleton.elim _ _
  rfl

@[simp]
theorem map_equivOfId_base (F : P.OrbitSumRealization b 1) :
    b.map F.equivOfId = F.base := by
  obtain rfl : F = ofId P b := Subsingleton.elim _ _
  rfl

end Id

/-! ### Transport along intertwining equivalences -/

section Transport

variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂} {σ : P.Aut} {σ₂ : P₂.Aut}

private theorem indexEquiv_comm_of_weightMap_comm (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) (j : ι) :
    e.indexEquiv (σ.indexEquiv j) = σ₂.indexEquiv (e.indexEquiv j) := by
  apply P₂.root.injective
  rw [← Hom.root_weightMap_apply, ← Hom.root_weightMap_apply, hσ,
    Hom.root_weightMap_apply, Hom.root_weightMap_apply]

/-- Restriction of an intertwining weight equivalence to the fixed submodules. -/
private noncomputable def fixedSubmoduleEquiv (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) :
    LinearMap.fixedSubmodule σ.weightMap ≃ₗ[R] LinearMap.fixedSubmodule σ₂.weightMap where
  toFun x := ⟨e.weightMap x.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    rw [← hσ, LinearMap.mem_fixedSubmodule_iff.mp x.2]⟩
  invFun y := ⟨e.weightEquiv.symm y.1, LinearMap.mem_fixedSubmodule_iff.mpr <| by
    apply e.bijective_weightMap.injective
    rw [hσ, Equiv.weightMap_weightEquiv_symm, LinearMap.mem_fixedSubmodule_iff.mp y.2]⟩
  left_inv x := Subtype.ext (e.weightEquiv_symm_weightMap x.1)
  right_inv y := Subtype.ext (e.weightMap_weightEquiv_symm y.1)
  map_add' x y := Subtype.ext (map_add e.weightMap x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul e.weightMap c x.1)

variable [Finite ι] [Finite ι₂] {b : P.Base} {b₂ : P₂.Base}

/-- Bijection between the distinct orbit-sum index sets induced by an intertwining equivalence. -/
private noncomputable def foldedIndicesEquiv (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) :
    P.foldedIndices σ ≃ P₂.foldedIndices σ₂ where
  toFun x := ⟨e.weightMap x.1, mem_foldedIndices.mpr <| by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp x.2
    refine ⟨e.indexEquiv i, ?_⟩
    rw [← weightMap_orbitSum e (indexEquiv_comm_of_weightMap_comm e hσ) i, hi]⟩
  invFun y := ⟨e.weightEquiv.symm y.1, mem_foldedIndices.mpr <| by
    obtain ⟨j, hj⟩ := mem_foldedIndices.mp y.2
    refine ⟨e.indexEquiv.symm j, ?_⟩
    apply e.bijective_weightMap.injective
    rw [Equiv.weightMap_weightEquiv_symm,
      weightMap_orbitSum e (indexEquiv_comm_of_weightMap_comm e hσ),
      _root_.Equiv.apply_symm_apply, hj]⟩
  left_inv x := Subtype.ext (e.weightEquiv_symm_weightMap x.1)
  right_inv y := Subtype.ext (e.weightMap_weightEquiv_symm y.1)

private noncomputable def mapPairing (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) :
    RootPairing (P₂.foldedIndices σ₂) R (LinearMap.fixedSubmodule σ₂.weightMap)
      (Module.Dual R (LinearMap.fixedSubmodule σ₂.weightMap)) :=
  F.pairing.map (foldedIndicesEquiv e hσ) (fixedSubmoduleEquiv e hσ)
    (fixedSubmoduleEquiv e hσ).symm.dualMap

private noncomputable def mapPairingEquiv (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) :
    F.pairing.Equiv (F.mapPairing e hσ) :=
  equivMap F.pairing (foldedIndicesEquiv e hσ) (fixedSubmoduleEquiv e hσ)
    (fixedSubmoduleEquiv e hσ).symm.dualMap

/-- **Transport of an orbit-sum realization** along a based equivalence `e : P.Equiv P₂`
intertwining `σ` and `σ₂`. -/
noncomputable def map (F : P.OrbitSumRealization b σ) (e : P.Equiv P₂)
    (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x))
    (hb : b.map e = b₂) : P₂.OrbitSumRealization b₂ σ₂ where
  pairing := F.mapPairing e hσ
  base := F.base.map (F.mapPairingEquiv e hσ)
  rootSystem := inferInstanceAs ((F.pairing.map _ _ _).IsRootSystem)
  reduced := isReduced_of_equiv (F.mapPairingEquiv e hσ)
  crystallographic := (F.mapPairingEquiv e hσ).toHom.isValuedIn ℤ
  evaluation x y := by
    simp only [mapPairing, RootPairing.map, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.dualMap_apply, LinearMap.toPerfPair_apply, F.evaluation]
    simp
  root_eq i := by
    obtain ⟨j, rfl⟩ := (foldedIndicesEquiv e hσ).surjective i
    simp [mapPairing, RootPairing.map, fixedSubmoduleEquiv, foldedIndicesEquiv, F.root_eq]
  base_eq i := by
    classical
    have hcomm := indexEquiv_comm_of_weightMap_comm e hσ
    rw [F.base.support_map_eq, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨j, hj, hjx⟩ := (F.base_eq x).mp hx
      refine ⟨e.indexEquiv j, ?_, ?_⟩
      · rw [← hb, b.support_map_eq]
        exact Finset.mem_image_of_mem _ hj
      · rw [← weightMap_orbitSum e hcomm j, hjx]
        rfl
    · rintro ⟨k, hk, hki⟩
      rw [← hb, b.support_map_eq, Finset.mem_image] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      refine ⟨⟨P.orbitSum σ j, P.orbitSum_mem_foldedIndices σ j⟩,
        F.orbitSum_mem_base_support hj, ?_⟩
      apply Subtype.ext
      simpa [mapPairingEquiv, equivMap, foldedIndicesEquiv, weightMap_orbitSum e hcomm j] using hki

section EquivOfEquiv

variable [IsDomain R] [CharZero R]
  (F₁ : P.OrbitSumRealization b σ) (F₂ : P₂.OrbitSumRealization b₂ σ₂) (e : P.Equiv P₂)
  (hσ : ∀ x, e.weightMap (σ.weightMap x) = σ₂.weightMap (e.weightMap x)) (hb : b.map e = b₂)

/-- **Induced equivalence of realizations**: any based equivalence `e : P.Equiv P₂` intertwining `σ`
and `σ₂` induces a canonical based equivalence `F₁.pairing.Equiv F₂.pairing` whose weight map is
the restriction of `e.weightMap` to fixed vectors. -/
noncomputable def equivOfEquiv : F₁.pairing.Equiv F₂.pairing :=
  (Subsingleton.elim (F₁.map e hσ hb) F₂) ▸ F₁.mapPairingEquiv e hσ

@[simp]
theorem coe_equivOfEquiv_weightMap (x : LinearMap.fixedSubmodule σ.weightMap) :
    (((F₁.equivOfEquiv F₂ e hσ hb).weightMap x : LinearMap.fixedSubmodule σ₂.weightMap) : M₂) =
      e.weightMap (x : M) := by
  obtain rfl : F₂ = F₁.map e hσ hb := Subsingleton.elim _ _
  rfl

@[simp]
theorem coe_equivOfEquiv_indexEquiv (i : P.foldedIndices σ) :
    (((F₁.equivOfEquiv F₂ e hσ hb).indexEquiv i : P₂.foldedIndices σ₂) : M₂) =
      e.weightMap (i : M) := by
  obtain rfl : F₂ = F₁.map e hσ hb := Subsingleton.elim _ _
  rfl

@[simp]
theorem map_equivOfEquiv_base : F₁.base.map (F₁.equivOfEquiv F₂ e hσ hb) = F₂.base := by
  obtain rfl : F₂ = F₁.map e hσ hb := Subsingleton.elim _ _
  rfl

end EquivOfEquiv

end Transport

end OrbitSumRealization

end RootPairing
