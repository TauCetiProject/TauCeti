/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.UnitWeight
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FinAdd

/-!
# Iteration compatibility of completed Gauss comparisons

Over a complete ultrametric normed commutative Huber ring `R`, splitting `Fin (k + m)` into an
inner block of `k` variables and an outer block of `m` variables yields two isomorphic ways to
iterate restricted power series:

1. On the Huber side, `TauCeti.Huber.iterateRingEquiv` identifies the completed weighted algebra
   `R⟨X₁, …, X_{k+m}⟩_U` with the iterated completion `R⟨X₁, …, Xₖ⟩_T⟨Y₁, …, Y_m⟩_W`.
2. On the Gauss-normed side, `TauCeti.MvPowerSeries.restrictedFinAddEquiv` identifies
   `R{X₁/r₁, …, X_{k+m}/r_{k+m}}` with
   `R{X₁/r₁, …, Xₖ/rₖ}{Y₁/r_{k+1}, …, Y_m/r_{k+m}}`.

When `U` consists of multiplicative units `uₗ` (`TauCeti.IsNormMulUnit`) with `‖uₗ‖ * rₗ = 1`, the
first block `T` compares with `R{X₁/r₁, …, Xₖ/rₖ}` via
`TauCeti.Huber.weightedRestrictedCompletionGaussEquiv`, and transporting coefficients along that
homeomorphism identifies the outer weights `W` with the constant-series images of the last `m`
units in `R{X₁/r₁, …, Xₖ/rₖ}`, which remain multiplicative units because `algebraMap` preserves
Gauss norms. Composing with the outer unit-weight Gauss comparison gives a topological ring
isomorphism `TauCeti.Huber.weightedIteratedCompletionGaussEquiv` on the iterated Huber completion,
making the square with `iterateSplitHom`, `iterateJoinHom`, `iterateFirstBlockHom`, and
`restrictedFinAddEquiv` commute.

A companion section establishes the same commutative square for the trivial-weight completed
algebras `TauCeti.Huber.restrictedMvPowerSeriesCompletion` and unit-radius Gauss-normed algebras,
without assuming `NormOneClass R` (so the trivial zero ring is not excluded).

## Main definitions

* `TauCeti.Huber.weightedIteratedCompletionGaussEquiv` and
  `TauCeti.Huber.weightedIteratedCompletionGaussAlgEquiv`: the topological ring and `R`-algebra
  equivalences from an iterated unit-weight Huber completion to the iterated Gauss-normed algebra.
* `TauCeti.Huber.restrictedIteratedCompletionGaussEquiv` and
  `TauCeti.Huber.restrictedIteratedCompletionGaussAlgEquiv`: the unit-radius trivial-weight iterated
  Gauss comparisons on `R⟨X₁, …, Xₖ⟩⟨Y₁, …, Y_m⟩`.

## Main results

* `TauCeti.Huber.weightedIteratedCompletionGaussEquiv_iterateSplitHom`,
  `TauCeti.Huber.weightedIteratedCompletionGaussEquiv_iterateRingEquiv`, and
  `TauCeti.Huber.weightedIteratedCompletionGaussAlgEquiv_iterateAlgEquiv`: splitting variables in
  the completed unit-weight Huber algebra commutes with `restrictedFinAddEquiv` and
  `restrictedFinAddAlgEquiv`.
* `TauCeti.Huber.weightedRestrictedCompletionGaussEquiv_iterateJoinHom` and
  `TauCeti.Huber.restrictedFinAddEquiv_weightedRestrictedCompletionGaussEquiv_iterateFirstBlockHom`:
  compatibility of the inverse join map and first-block inclusion with the Gauss comparisons.
* `TauCeti.Huber.restrictedIteratedCompletionGaussEquiv_iterateSplitHom`,
  `TauCeti.Huber.restrictedIteratedCompletionGaussEquiv_iterateRingEquiv`,
  `TauCeti.Huber.restrictedIteratedCompletionGaussAlgEquiv_iterateAlgEquiv`, and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom`: the corresponding
  unit-radius compatibilities for `restrictedMvPowerSeriesCompletion`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* T. Wedhorn, *Adic Spaces*, §5.6, Propositions 5.49 and 5.50.
-/

public section

namespace TauCeti.Huber

open UniformSpace _root_.MvPowerSeries TauCeti.MvPowerSeries

/-! ### Iterated Gauss comparison for multiplicative-unit weights -/

private theorem weightedMapCompletionEquiv_coe_weightedC {n : ℕ} {A B : Type*}
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {T : Fin n → Set A} {S : Fin n → Set B}
    (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, (e : A →+* B) '' T i ⊆ S i)
    (hST : ∀ i, (e.symm : B →+* A) '' S i ⊆ T i) (a : A) :
    weightedMapCompletionEquiv e he he' hT hS hTS hST
        ((weightedC T hT a : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) =
      ((weightedC S hS (e a) : weightedRestrictedSubring S hS) :
        Completion (weightedRestrictedSubring S hS)) :=
  (weightedMapCompletionEquiv_apply e he he' hT hS hTS hST _).trans <|
    (weightedMapCompletion_coe (φ := (e : A →+* B)) he hT hS hTS _).trans
      (congrArg _ (weightedMap_weightedC (φ := (e : A →+* B)) he hTS a))

private theorem weightedMapCompletionEquiv_coe_weightedX {n : ℕ} {A B : Type*}
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    {T : Fin n → Set A} {S : Fin n → Set B}
    (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, (e : A →+* B) '' T i ⊆ S i)
    (hST : ∀ i, (e.symm : B →+* A) '' S i ⊆ T i) (i : Fin n) :
    weightedMapCompletionEquiv e he he' hT hS hTS hST
        ((weightedX T hT i : weightedRestrictedSubring T hT) :
          Completion (weightedRestrictedSubring T hT)) =
      ((weightedX S hS i : weightedRestrictedSubring S hS) :
        Completion (weightedRestrictedSubring S hS)) :=
  (weightedMapCompletionEquiv_apply e he he' hT hS hTS hST _).trans <|
    (weightedMapCompletion_coe (φ := (e : A →+* B)) he hT hS hTS _).trans
      (congrArg _ (weightedMap_weightedX (φ := (e : A →+* B)) he hTS i))

section UnitWeightOuter

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  {r : Fin (k + m) → ℝ}

local notation "Inner" => IsRestricted.subring (R := R) (r ∘ Fin.castAdd m)
local notation "Flat" => IsRestricted.subring (R := R) r
local notation "Iter" => IsRestricted.subring (R := Inner) (r ∘ Fin.natAdd k)

/-- The last `m` units `u (Fin.natAdd k j)` mapped as constant series into the inner Gauss-normed
algebra. -/
private noncomputable def outerUnits (u : Fin (k + m) → Rˣ) : Fin m → Innerˣ :=
  fun j ↦ Units.map (algebraMap R Inner).toMonoidHom (u (Fin.natAdd k j))

@[simp]
private theorem coe_outerUnits (u : Fin (k + m) → Rˣ) (j : Fin m) :
    (outerUnits (r := r) u j : Inner) = algebraMap R Inner (u (Fin.natAdd k j) : R) := rfl

section NormedInner

variable [∀ l, Fact (0 < r l)]

private theorem isNormMulUnit_outerUnits (u : Fin (k + m) → Rˣ)
    (hu : ∀ l, IsNormMulUnit (u l : R)) :
    ∀ j, IsNormMulUnit (outerUnits (r := r) u j : Inner) :=
  fun j ↦ (hu (Fin.natAdd k j)).map (algebraMap R Inner).toMonoidHom
    norm_algebraMap_isRestrictedSubring

private theorem norm_outerUnits_mul_eq_one (u : Fin (k + m) → Rˣ)
    (hr : ∀ l, ‖(u l : R)‖ * r l = 1) :
    ∀ j, ‖(outerUnits (r := r) u j : Inner)‖ * (r ∘ Fin.natAdd k) j = 1 := fun j ↦ by
  rw [coe_outerUnits, norm_algebraMap_isRestrictedSubring]
  exact hr (Fin.natAdd k j)

end NormedInner

variable [CompleteSpace R]

private theorem image_outerWeights (u : Fin (k + m) → Rˣ) (hu : ∀ l, IsNormMulUnit (u l : R))
    (hr : ∀ l, ‖(u l : R)‖ * r l = 1)
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i))))}
    (hUW : ∀ j,
      algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) ''
        ({(u (Fin.natAdd k j) : R)} : Set R) = W j) :
    ∀ j,
      ((weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
          (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)) : _ ≃+* _) :
        _ →+* _) '' W j ⊆
        {(outerUnits (r := r) u j : Inner)} := by
  rintro j _ ⟨w, hw, rfl⟩
  rw [← hUW j] at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [Set.mem_singleton_iff] at hx ⊢
  subst hx
  simp

private theorem symm_image_outerUnits (u : Fin (k + m) → Rˣ) (hu : ∀ l, IsNormMulUnit (u l : R))
    (hr : ∀ l, ‖(u l : R)‖ * r l = 1)
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i))))}
    (hUW : ∀ j,
      algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) ''
        ({(u (Fin.natAdd k j) : R)} : Set R) = W j) :
    ∀ j,
      (((weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
          (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i))).symm : _ ≃+* _) :
        _ →+* _) ''
        {(outerUnits (r := r) u j : Inner)} ⊆ W j := by
  rintro j _ ⟨y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← hUW j]
  refine ⟨(u (Fin.natAdd k j) : R), rfl, ?_⟩
  simp

variable [∀ l, Fact (0 < r l)] (u : Fin (k + m) → Rˣ) (hu : ∀ l, IsNormMulUnit (u l : R))
  (hr : ∀ l, ‖(u l : R)‖ * r l = 1)
  {W : Fin m → Set (Completion (weightedRestrictedSubring
    (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
    (isWeightFamily_units fun i ↦ u (Fin.castAdd m i))))}
  (hW : IsWeightFamily W)
  (hUW : ∀ j,
    algebraMap R (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)

/-- **Completed Gauss comparison for an iterated unit-weight Huber algebra.** Transporting
coefficients along the inner `weightedRestrictedCompletionGaussEquiv` and applying the outer
unit-weight comparison identifies `R⟨X₁, …, Xₖ⟩_T⟨Y₁, …, Y_m⟩_W` with
`R{X₁/r₁, …, Xₖ/rₖ}{Y₁/r_{k+1}, …, Y_m/r_{k+m}}`. -/
noncomputable def weightedIteratedCompletionGaussEquiv :
    Completion (weightedRestrictedSubring W hW) ≃+* Iter :=
  (weightedMapCompletionEquiv
    (weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
      (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)))
    (continuous_weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
      (fun i ↦ u (Fin.castAdd m i)) (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)))
    (continuous_weightedRestrictedCompletionGaussEquiv_symm (c := r ∘ Fin.castAdd m)
      (fun i ↦ u (Fin.castAdd m i)) (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)))
    hW (isWeightFamily_units (outerUnits (r := r) u))
    (image_outerWeights u hu hr hUW)
    (symm_image_outerUnits u hu hr hUW)).trans
    (weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.natAdd k) (outerUnits (r := r) u)
      (isNormMulUnit_outerUnits u hu) (norm_outerUnits_mul_eq_one u hr))

/-- The iterated unit-weight Gauss comparison is continuous. -/
theorem continuous_weightedIteratedCompletionGaussEquiv :
    Continuous (weightedIteratedCompletionGaussEquiv u hu hr hW hUW) := by
  rw [weightedIteratedCompletionGaussEquiv, RingEquiv.coe_trans]
  exact (continuous_weightedRestrictedCompletionGaussEquiv _ _ _).comp
    (continuous_weightedMapCompletionEquiv _ _ _ _ _ _ _)

/-- The inverse iterated unit-weight Gauss comparison is continuous. -/
theorem continuous_weightedIteratedCompletionGaussEquiv_symm :
    Continuous (weightedIteratedCompletionGaussEquiv u hu hr hW hUW).symm := by
  rw [weightedIteratedCompletionGaussEquiv, RingEquiv.symm_trans, RingEquiv.coe_trans]
  exact (continuous_weightedMapCompletionEquiv_symm _ _ _ _ _ _ _).comp
    (continuous_weightedRestrictedCompletionGaussEquiv_symm _ _ _)

/-- On a constant series of the outer algebra, `weightedIteratedCompletionGaussEquiv` applies the
inner Gauss comparison and embeds the result as a constant series of the outer Gauss-normed
algebra. -/
@[simp]
theorem weightedIteratedCompletionGaussEquiv_coe_weightedC
    (c : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        ((weightedC W hW c : weightedRestrictedSubring W hW) :
          Completion (weightedRestrictedSubring W hW)) =
      algebraMap Inner Iter
        (weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
          (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)) c) := by
  rw [weightedIteratedCompletionGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedC, weightedRestrictedCompletionGaussEquiv_coe_weightedC]

/-- On `algebraMap` from the inner completion, `weightedIteratedCompletionGaussEquiv` acts via the
inner Gauss comparison. -/
theorem weightedIteratedCompletionGaussEquiv_algebraMap
    (c : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        (algebraMap _ (Completion (weightedRestrictedSubring W hW)) c) =
      algebraMap Inner Iter
        (weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
          (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)) c) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply,
    weightedIteratedCompletionGaussEquiv_coe_weightedC]

/-- On the `j`-th outer variable, `weightedIteratedCompletionGaussEquiv` gives `X j`. -/
@[simp]
theorem weightedIteratedCompletionGaussEquiv_coe_weightedX (j : Fin m) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        ((weightedX W hW j : weightedRestrictedSubring W hW) :
          Completion (weightedRestrictedSubring W hW)) =
      ⟨X j, isRestricted_X (r ∘ Fin.natAdd k) j⟩ := by
  rw [weightedIteratedCompletionGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedX, weightedRestrictedCompletionGaussEquiv_coe_weightedX]

end UnitWeightOuter

section UnitWeightIterate

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [IsHuberRing R]
  (u : Fin (k + m) → Rˣ) (hu : ∀ l, IsNormMulUnit (u l : R))
  {r : Fin (k + m) → ℝ} [∀ l, Fact (0 < r l)] (hr : ∀ l, ‖(u l : R)‖ * r l = 1)
  {W : Fin m → Set (Completion (weightedRestrictedSubring
    (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
    (isWeightFamily_units fun i ↦ u (Fin.castAdd m i))))}
  (hW : IsWeightFamily W)
  (hUW : ∀ j,
    algebraMap R (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)

local notation "Inner" => IsRestricted.subring (R := R) (r ∘ Fin.castAdd m)
local notation "Flat" => IsRestricted.subring (R := R) r
local notation "Iter" => IsRestricted.subring (R := Inner) (r ∘ Fin.natAdd k)

/-- `weightedIteratedCompletionGaussEquiv` intertwines `iterateStructureHom` with `algebraMap R`
into the iterated Gauss-normed algebra. -/
theorem weightedIteratedCompletionGaussEquiv_iterateStructureHom (a : R) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW a) =
      algebraMap R Iter a := by
  simp [← IsScalarTower.algebraMap_apply R Inner Iter]

/-- **Iterated unit-weight Gauss comparison as an `R`-algebra equivalence**, with respect to the
`R`-algebra structure induced by `iterateStructureHom`. -/
noncomputable def weightedIteratedCompletionGaussAlgEquiv :
    letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
    Completion (weightedRestrictedSubring W hW) ≃ₐ[R] Iter :=
  letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
  AlgEquiv.ofRingEquiv (f := weightedIteratedCompletionGaussEquiv u hu hr hW hUW) fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra,
      weightedIteratedCompletionGaussEquiv_iterateStructureHom]

/-- The underlying `RingEquiv` of `weightedIteratedCompletionGaussAlgEquiv` is
`weightedIteratedCompletionGaussEquiv`. -/
@[simp]
theorem weightedIteratedCompletionGaussAlgEquiv_toRingEquiv :
    letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
    (weightedIteratedCompletionGaussAlgEquiv u hu hr hW hUW).toRingEquiv =
      weightedIteratedCompletionGaussEquiv u hu hr hW hUW := (rfl)

/-- Pointwise coercion of `weightedIteratedCompletionGaussAlgEquiv`. -/
@[simp]
theorem weightedIteratedCompletionGaussAlgEquiv_apply
    (x : Completion (weightedRestrictedSubring W hW)) :
    letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
    weightedIteratedCompletionGaussAlgEquiv u hu hr hW hUW x =
      weightedIteratedCompletionGaussEquiv u hu hr hW hUW x := (rfl)

/-- Pointwise coercion of `weightedIteratedCompletionGaussAlgEquiv.symm`. -/
@[simp]
theorem weightedIteratedCompletionGaussAlgEquiv_symm_apply (y : Iter) :
    letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
    (weightedIteratedCompletionGaussAlgEquiv u hu hr hW hUW).symm y =
      (weightedIteratedCompletionGaussEquiv u hu hr hW hUW).symm y := (rfl)

/-- **Huber iteration splitting commutes with Gauss-normed variable splitting** at
multiplicative-unit weights. -/
theorem weightedIteratedCompletionGaussEquiv_iterateSplitHom
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R))
    (x : Completion (weightedRestrictedSubring
      (fun l ↦ ({(u l : R)} : Set R)) (isWeightFamily_units u))) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        (iterateSplitHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
          (isWeightFamily_units u) hTU hUW x) =
      restrictedFinAddEquiv (weightedRestrictedCompletionGaussEquiv u hu hr x) := by
  have hhom :
      (weightedIteratedCompletionGaussEquiv u hu hr hW hUW).toRingHom.comp
          (iterateSplitHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
            (isWeightFamily_units u) hTU hUW) =
        restrictedFinAddEquiv.toRingHom.comp
          (weightedRestrictedCompletionGaussEquiv u hu hr).toRingHom := by
    refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous (isWeightFamily_units u)
      ((continuous_weightedIteratedCompletionGaussEquiv u hu hr hW hUW).comp
        (continuous_iterateSplitHom ..))
      (isometry_restrictedFinAddEquiv.continuous.comp
        (continuous_weightedRestrictedCompletionGaussEquiv u hu hr))
      (fun a ↦ ?_) fun l ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l
    · simp [← IsScalarTower.algebraMap_apply R Inner Iter]
    · simp
    · simp
  exact DFunLike.congr_fun hhom x

/-- **`iterateRingEquiv` commutes with the completed unit-weight Gauss comparisons.** -/
theorem weightedIteratedCompletionGaussEquiv_iterateRingEquiv
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R))
    (x : Completion (weightedRestrictedSubring
      (fun l ↦ ({(u l : R)} : Set R)) (isWeightFamily_units u))) :
    weightedIteratedCompletionGaussEquiv u hu hr hW hUW
        (iterateRingEquiv (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
          (isWeightFamily_units u) hTU hUW x) =
      restrictedFinAddEquiv (weightedRestrictedCompletionGaussEquiv u hu hr x) := by
  rw [iterateRingEquiv_apply,
    weightedIteratedCompletionGaussEquiv_iterateSplitHom u hu hr hW hUW hTU]

/-- **Commutative square of `R`-algebra equivalences** between `iterateAlgEquiv` and
`restrictedFinAddAlgEquiv` at multiplicative-unit weights. -/
theorem weightedIteratedCompletionGaussAlgEquiv_iterateAlgEquiv
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R)) :
    letI := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
    (iterateAlgEquiv (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
        (isWeightFamily_units u) hTU hUW).trans
      (weightedIteratedCompletionGaussAlgEquiv u hu hr hW hUW) =
      (weightedRestrictedCompletionGaussAlgEquiv u hu hr).trans
        (restrictedFinAddAlgEquiv (S := R)) := by
  let _ := (iterateStructureHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW).toAlgebra
  refine AlgEquiv.ext fun x ↦ ?_
  simpa using weightedIteratedCompletionGaussEquiv_iterateRingEquiv u hu hr hW hUW hTU x

/-- **Huber iteration joining commutes with `restrictedFinAddEquiv.symm`** at multiplicative-unit
weights. -/
theorem weightedRestrictedCompletionGaussEquiv_iterateJoinHom
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R))
    (y : Completion (weightedRestrictedSubring W hW)) :
    weightedRestrictedCompletionGaussEquiv u hu hr
        (iterateJoinHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
          (isWeightFamily_units u) hTU hUW y) =
      restrictedFinAddEquiv.symm
        (weightedIteratedCompletionGaussEquiv u hu hr hW hUW y) := by
  apply restrictedFinAddEquiv.injective
  rw [RingEquiv.apply_symm_apply,
    ← weightedIteratedCompletionGaussEquiv_iterateSplitHom u hu hr hW hUW hTU]
  exact congrArg (weightedIteratedCompletionGaussEquiv u hu hr hW hUW)
    (DFunLike.congr_fun (iterateSplitHom_comp_iterateJoinHom ..) y)

/-- **`(iterateRingEquiv ...).symm` commutes with `restrictedFinAddEquiv.symm`.** -/
theorem weightedRestrictedCompletionGaussEquiv_iterateRingEquiv_symm
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R))
    (y : Completion (weightedRestrictedSubring W hW)) :
    weightedRestrictedCompletionGaussEquiv u hu hr
        ((iterateRingEquiv (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)) hW
          (isWeightFamily_units u) hTU hUW).symm y) =
      restrictedFinAddEquiv.symm
        (weightedIteratedCompletionGaussEquiv u hu hr hW hUW y) := by
  rw [iterateRingEquiv_symm_apply,
    weightedRestrictedCompletionGaussEquiv_iterateJoinHom u hu hr hW hUW hTU]

/-- **First-block inclusion compatibility.** Including the first `k` variables via
`iterateFirstBlockHom` and splitting along `restrictedFinAddEquiv` embeds the inner Gauss-normed
series as a constant series of the outer algebra. -/
theorem restrictedFinAddEquiv_weightedRestrictedCompletionGaussEquiv_iterateFirstBlockHom
    (hTU : ∀ i,
      ({(u (Fin.castAdd m i) : R)} : Set R) = ({(u (Fin.castAdd m i) : R)} : Set R))
    (c : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))) :
    restrictedFinAddEquiv
        (weightedRestrictedCompletionGaussEquiv u hu hr
          (iterateFirstBlockHom (isWeightFamily_units fun i ↦ u (Fin.castAdd m i))
            (isWeightFamily_units u) hTU c)) =
      algebraMap Inner Iter
        (weightedRestrictedCompletionGaussEquiv (c := r ∘ Fin.castAdd m)
          (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hr (Fin.castAdd m i)) c) := by
  let B := Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units fun i ↦ u (Fin.castAdd m i)))
  let w : Fin m → Bˣ :=
    fun j ↦ Units.map (algebraMap R B).toMonoidHom (u (Fin.natAdd k j))
  have hUW₀ : ∀ j,
      algebraMap R B '' ({(u (Fin.natAdd k j) : R)} : Set R) = {(w j : B)} := fun j ↦ by
    simp [w]
  rw [← weightedIteratedCompletionGaussEquiv_iterateSplitHom u hu hr
      (isWeightFamily_units w) hUW₀ hTU,
    ← RingHom.comp_apply, iterateSplitHom_comp_iterateFirstBlockHom,
    weightedIteratedCompletionGaussEquiv_algebraMap]

end UnitWeightIterate

/-! ### Unit-radius iteration compatibility for `restrictedMvPowerSeriesCompletion` -/

section OneWeightIterate

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

local notation "Inner₁" => IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ))
local notation "Flat₁" => IsRestricted.subring (R := R) (fun _ : Fin (k + m) ↦ (1 : ℝ))
local notation "Iter₁" => IsRestricted.subring (R := Inner₁) (fun _ : Fin m ↦ (1 : ℝ))

/-- **Iterated unit-radius Gauss comparison** identifying `R⟨X₁, …, Xₖ⟩⟨Y₁, …, Y_m⟩` with
`R{X₁, …, Xₖ}{Y₁, …, Y_m}`, without requiring `NormOneClass R`. -/
noncomputable def restrictedIteratedCompletionGaussEquiv :
    restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R) ≃+* Iter₁ :=
  (weightedMapCompletionEquiv
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm
    isWeightFamily_one_weight isWeightFamily_one_weight
    (fun _ ↦ by simp) (fun _ ↦ by simp)).trans
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := m) (R := Inner₁))

/-- `restrictedIteratedCompletionGaussEquiv` is continuous. -/
theorem continuous_restrictedIteratedCompletionGaussEquiv :
    Continuous (restrictedIteratedCompletionGaussEquiv (k := k) (m := m) (R := R)) := by
  rw [restrictedIteratedCompletionGaussEquiv, RingEquiv.coe_trans]
  exact continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
    (continuous_weightedMapCompletionEquiv _ _ _ _ _ _ _)

/-- The inverse of `restrictedIteratedCompletionGaussEquiv` is continuous. -/
theorem continuous_restrictedIteratedCompletionGaussEquiv_symm :
    Continuous (restrictedIteratedCompletionGaussEquiv (k := k) (m := m) (R := R)).symm := by
  rw [restrictedIteratedCompletionGaussEquiv, RingEquiv.symm_trans, RingEquiv.coe_trans]
  exact (continuous_weightedMapCompletionEquiv_symm _ _ _ _ _ _ _).comp
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm

/-- On a constant series of the outer algebra, `restrictedIteratedCompletionGaussEquiv` applies the
inner unit-radius Gauss comparison and embeds the result as a constant series. -/
@[simp]
theorem restrictedIteratedCompletionGaussEquiv_coe_weightedC
    (c : restrictedMvPowerSeriesCompletion k R) :
    restrictedIteratedCompletionGaussEquiv
        ((weightedC _ isWeightFamily_one_weight c :
          weightedRestrictedSubring
            (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
            isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) =
      algebraMap Inner₁ Iter₁ (restrictedMvPowerSeriesCompletionGaussEquiv c) := by
  rw [restrictedIteratedCompletionGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedC,
    restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedC]

/-- On `algebraMap` from the inner completion, `restrictedIteratedCompletionGaussEquiv` acts via
`restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem restrictedIteratedCompletionGaussEquiv_algebraMap
    (c : restrictedMvPowerSeriesCompletion k R) :
    restrictedIteratedCompletionGaussEquiv
        (algebraMap (restrictedMvPowerSeriesCompletion k R)
          (restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) c) =
      algebraMap Inner₁ Iter₁ (restrictedMvPowerSeriesCompletionGaussEquiv c) := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply,
    restrictedIteratedCompletionGaussEquiv_coe_weightedC]

/-- On the `j`-th outer variable, `restrictedIteratedCompletionGaussEquiv` gives `X j`. -/
@[simp]
theorem restrictedIteratedCompletionGaussEquiv_coe_weightedX (j : Fin m) :
    restrictedIteratedCompletionGaussEquiv
        ((weightedX _ isWeightFamily_one_weight j :
          weightedRestrictedSubring
            (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
            isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) =
      ⟨X j, isRestricted_X (fun _ : Fin m ↦ 1) j⟩ := by
  rw [restrictedIteratedCompletionGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedX,
    restrictedMvPowerSeriesCompletionGaussEquiv_coe,
    restrictedMvPowerSeriesGaussEquiv_weightedX]

variable [IsHuberRing R]

/-- `restrictedIteratedCompletionGaussEquiv` intertwines `iterateStructureHom` at trivial weights
with `algebraMap R` into the iterated unit-radius Gauss-normed algebra. -/
theorem restrictedIteratedCompletionGaussEquiv_iterateStructureHom (a : R) :
    restrictedIteratedCompletionGaussEquiv
        (iterateStructureHom (k := k) (m := m) isWeightFamily_one_weight
          isWeightFamily_one_weight a) =
      algebraMap R Iter₁ a := by
  simp [← IsScalarTower.algebraMap_apply R Inner₁ Iter₁]

/-- **Iterated unit-radius Gauss comparison as an `R`-algebra equivalence**, with respect to the
`R`-algebra structure induced by `iterateStructureHom`. -/
noncomputable def restrictedIteratedCompletionGaussAlgEquiv :
    letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
      isWeightFamily_one_weight).toAlgebra
    restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R) ≃ₐ[R] Iter₁ :=
  letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
    isWeightFamily_one_weight).toAlgebra
  AlgEquiv.ofRingEquiv (f := restrictedIteratedCompletionGaussEquiv) fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra,
      restrictedIteratedCompletionGaussEquiv_iterateStructureHom]

/-- The underlying `RingEquiv` of `restrictedIteratedCompletionGaussAlgEquiv` is
`restrictedIteratedCompletionGaussEquiv`. -/
@[simp]
theorem restrictedIteratedCompletionGaussAlgEquiv_toRingEquiv :
    letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
      isWeightFamily_one_weight).toAlgebra
    (restrictedIteratedCompletionGaussAlgEquiv (k := k) (m := m) (R := R)).toRingEquiv =
      restrictedIteratedCompletionGaussEquiv := (rfl)

/-- Pointwise coercion of `restrictedIteratedCompletionGaussAlgEquiv`. -/
@[simp]
theorem restrictedIteratedCompletionGaussAlgEquiv_apply
    (x : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) :
    letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
      isWeightFamily_one_weight).toAlgebra
    restrictedIteratedCompletionGaussAlgEquiv x = restrictedIteratedCompletionGaussEquiv x :=
  (rfl)

/-- Pointwise coercion of `restrictedIteratedCompletionGaussAlgEquiv.symm`. -/
@[simp]
theorem restrictedIteratedCompletionGaussAlgEquiv_symm_apply (y : Iter₁) :
    letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
      isWeightFamily_one_weight).toAlgebra
    (restrictedIteratedCompletionGaussAlgEquiv (k := k) (m := m) (R := R)).symm y =
      restrictedIteratedCompletionGaussEquiv.symm y := (rfl)

/-- **Trivial-weight `iterateSplitHom` commutes with `restrictedFinAddEquiv`** across the completed
unit-radius Gauss comparisons. -/
theorem restrictedIteratedCompletionGaussEquiv_iterateSplitHom
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    restrictedIteratedCompletionGaussEquiv
        (iterateSplitHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight hTU hUW x) =
      restrictedFinAddEquiv (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  have hhom :
      restrictedIteratedCompletionGaussEquiv.toRingHom.comp
          (iterateSplitHom isWeightFamily_one_weight isWeightFamily_one_weight
            isWeightFamily_one_weight hTU hUW) =
        (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).toRingHom.comp
          restrictedMvPowerSeriesCompletionGaussEquiv.toRingHom := by
    refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (continuous_restrictedIteratedCompletionGaussEquiv.comp (continuous_iterateSplitHom ..))
      (isometry_restrictedFinAddEquiv.continuous.comp
        continuous_restrictedMvPowerSeriesCompletionGaussEquiv)
      (fun a ↦ ?_) fun l ↦ Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, iterateSplitHom_coe_weightedC,
        restrictedIteratedCompletionGaussEquiv_iterateStructureHom,
        restrictedMvPowerSeriesCompletionGaussEquiv_coe,
        restrictedMvPowerSeriesGaussEquiv_weightedC, restrictedFinAddEquiv_algebraMap]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, iterateSplitHom_coe_weightedX, iterateVar_castAdd,
        restrictedIteratedCompletionGaussEquiv_coe_weightedC,
        restrictedMvPowerSeriesCompletionGaussEquiv_coe,
        restrictedMvPowerSeriesGaussEquiv_weightedX]
      exact (restrictedFinAddEquiv_X_castAdd (R := R) (r := fun _ : Fin (k + m) ↦ (1 : ℝ)) i).symm
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, iterateSplitHom_coe_weightedX, iterateVar_natAdd,
        restrictedIteratedCompletionGaussEquiv_coe_weightedX,
        restrictedMvPowerSeriesCompletionGaussEquiv_coe,
        restrictedMvPowerSeriesGaussEquiv_weightedX]
      exact (restrictedFinAddEquiv_X_natAdd (R := R) (r := fun _ : Fin (k + m) ↦ (1 : ℝ)) j).symm
  exact DFunLike.congr_fun hhom x

/-- **Trivial-weight `iterateRingEquiv` commutes with `restrictedFinAddEquiv`** across the
completed unit-radius Gauss comparisons. -/
theorem restrictedIteratedCompletionGaussEquiv_iterateRingEquiv
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    restrictedIteratedCompletionGaussEquiv
        (iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight hTU hUW x) =
      restrictedFinAddEquiv (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  rw [iterateRingEquiv_apply, restrictedIteratedCompletionGaussEquiv_iterateSplitHom hTU hUW]

/-- **Commutative square of `R`-algebra equivalences** between trivial-weight `iterateAlgEquiv` and
unit-radius `restrictedFinAddAlgEquiv`. -/
theorem restrictedIteratedCompletionGaussAlgEquiv_iterateAlgEquiv
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R))) :
    letI := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
      isWeightFamily_one_weight).toAlgebra
    (iterateAlgEquiv isWeightFamily_one_weight isWeightFamily_one_weight
        isWeightFamily_one_weight hTU hUW).trans
      restrictedIteratedCompletionGaussAlgEquiv =
      restrictedMvPowerSeriesCompletionGaussAlgEquiv.trans
        (restrictedFinAddAlgEquiv (S := R) (r := fun _ : Fin (k + m) ↦ (1 : ℝ))) := by
  let _ := (iterateStructureHom (k := k) (m := m) (A := R) isWeightFamily_one_weight
    isWeightFamily_one_weight).toAlgebra
  refine AlgEquiv.ext fun x ↦ ?_
  simpa using restrictedIteratedCompletionGaussEquiv_iterateRingEquiv hTU hUW x

/-- **Trivial-weight `iterateJoinHom` commutes with `restrictedFinAddEquiv.symm`** across the
completed unit-radius Gauss comparisons. -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (y : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (iterateJoinHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight hTU hUW y) =
      (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).symm
        (restrictedIteratedCompletionGaussEquiv y) := by
  apply (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).injective
  rw [RingEquiv.apply_symm_apply, ← restrictedIteratedCompletionGaussEquiv_iterateSplitHom hTU hUW]
  exact congrArg restrictedIteratedCompletionGaussEquiv
    (DFunLike.congr_fun (iterateSplitHom_comp_iterateJoinHom ..) y)

/-- **Trivial-weight `(iterateRingEquiv ...).symm` commutes with `restrictedFinAddEquiv.symm`.** -/
theorem restrictedMvPowerSeriesCompletionGaussEquiv_iterateRingEquiv_symm
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (y : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        ((iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight hTU hUW).symm y) =
      (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).symm
        (restrictedIteratedCompletionGaussEquiv y) := by
  rw [iterateRingEquiv_symm_apply, restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom]

/-- **First-block inclusion compatibility at unit radius.** Including the first `k` variables via
`iterateFirstBlockHom` and splitting along `restrictedFinAddEquiv` embeds the inner unit-radius
restricted series as a constant series of the outer algebra. -/
theorem restrictedFinAddEquiv_restrictedMvPowerSeriesCompletionGaussEquiv_iterateFirstBlockHom
    (hTU : ∀ _ : Fin k, ({1} : Set R) = ({1} : Set R))
    (c : restrictedMvPowerSeriesCompletion k R) :
    (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ)))
        (restrictedMvPowerSeriesCompletionGaussEquiv
          (iterateFirstBlockHom (m := m) isWeightFamily_one_weight isWeightFamily_one_weight
            hTU c)) =
      algebraMap Inner₁ Iter₁ (restrictedMvPowerSeriesCompletionGaussEquiv c) := by
  have hUW : ∀ _ : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) '' ({1} : Set R) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)) := fun _ ↦ by simp
  rw [← restrictedIteratedCompletionGaussEquiv_iterateSplitHom hTU hUW,
    ← RingHom.comp_apply, iterateSplitHom_comp_iterateFirstBlockHom,
    restrictedIteratedCompletionGaussEquiv_algebraMap]

end OneWeightIterate

end TauCeti.Huber
