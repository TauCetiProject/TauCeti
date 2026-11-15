/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Topology.PiCurry

/-!
# Continuous linear regrouping of coordinate families

`ContinuousLinearEquiv.piOptionEquivProd` splits a dependent family indexed by `Option ι`
into its `none` coordinate and its `some` coordinates. It supplies product coordinates
for linear charts, with no finiteness or norm assumptions.

The construction combines `LinearEquiv.piOptionEquivProd` with
`TauCeti.piOptionEquivProdHomeomorph`.

For Mathlib's `ContinuousLinearEquiv.sumPiEquivProdPi`, which splits a family indexed by `S ⊕ T`
into its restrictions to `S` and to `T`, `ContinuousLinearEquiv.sumPiEquivProdPi_apply` and
`ContinuousLinearEquiv.sumPiEquivProdPi_symm_apply` evaluate the equivalence and its inverse.
`ContinuousLinearEquiv.negCoord` negates a single coordinate of a dependent product while leaving
the remaining coordinates fixed.

`TauCeti.piSigmaConstContinuousLinearEquiv` regroups a family of tuples along a bijection of its
sigma index. Its underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`, which is linear
coordinatewise, so coordinate calculations can use both the homeomorphism and the linear API.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R] {ι : Type*} {M : Option ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

/-- Split a family indexed by `Option ι` into its distinguished coordinate and the rest. -/
def piOptionEquivProd : ((i : Option ι) → M i) ≃L[R] M none × ((i : ι) → M (some i)) :=
  { toLinearEquiv := LinearEquiv.piOptionEquivProd R
    continuous_toFun := (TauCeti.piOptionEquivProdHomeomorph M).continuous.congr
      (fun x => TauCeti.piOptionEquivProdHomeomorph_apply M x)
    continuous_invFun := (TauCeti.piOptionEquivProdHomeomorph M).symm.continuous.congr
      (fun q => by
        funext i
        cases i <;> simp only [TauCeti.piOptionEquivProdHomeomorph_symm_apply_none,
          TauCeti.piOptionEquivProdHomeomorph_symm_apply_some] <;> rfl) }

/-- The split coordinates are the `none` value followed by the `some` values. -/
@[simp] theorem piOptionEquivProd_apply (x : (i : Option ι) → M i) :
    piOptionEquivProd R x = (x none, fun i => x (some i)) := (rfl)

/-- Reassemble an optional coordinate family from its distinguished value and the rest. -/
@[simp] theorem piOptionEquivProd_symm_apply (q : M none × ((i : ι) → M (some i))) :
    (piOptionEquivProd R).symm q = (fun i => match i with
      | none => q.1
      | some j => q.2 j) := by
  funext i
  cases i <;> rfl

section SumPi

variable {S T : Type*} {A : S ⊕ T → Type*} [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
  [∀ st, TopologicalSpace (A st)]

/-- Mathlib's `ContinuousLinearEquiv.sumPiEquivProdPi` restricts a family on `S ⊕ T` to `S` and
to `T`. -/
@[simp] theorem sumPiEquivProdPi_apply (x : (st : S ⊕ T) → A st) :
    sumPiEquivProdPi R S T A x = (fun s => x (.inl s), fun t => x (.inr t)) := (rfl)

/-- The inverse of `ContinuousLinearEquiv.sumPiEquivProdPi` glues a family on `S` and a family on
`T` into a family on `S ⊕ T`. -/
@[simp] theorem sumPiEquivProdPi_symm_apply
    (p : ((s : S) → A (.inl s)) × ((t : T) → A (.inr t))) :
    (sumPiEquivProdPi R S T A).symm p = Sum.rec p.1 p.2 := (rfl)

end SumPi

section NegCoord

variable {R} [DecidableEq ι] {N P : ι → Type*}
  [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, TopologicalSpace (P i)] [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- A coordinatewise continuous linear equivalence sends a one-point family to the one-point family
of its image in that coordinate. -/
@[simp]
theorem piCongrRight_single (e : ∀ i, N i ≃L[R] P i) (i : ι) (x : N i) :
    piCongrRight e (Pi.single i x) = Pi.single i (e i x) := by
  funext j
  rw [piCongrRight_apply]
  exact Pi.apply_single (fun i ↦ e i) (fun _ ↦ map_zero _) i x j

variable (R) {Q : ι → Type*} [∀ i, TopologicalSpace (Q i)] [∀ i, AddCommGroup (Q i)]
  [∀ i, Module R (Q i)] [∀ i, ContinuousNeg (Q i)]

/-- Negate the `k`-th coordinate of a dependent product while leaving all other coordinates
unchanged, as a continuous linear equivalence. -/
def negCoord (k : ι) : ((i : ι) → Q i) ≃L[R] (i : ι) → Q i :=
  piCongrRight (Function.update (fun i ↦ ContinuousLinearEquiv.refl R (Q i)) k (neg R))

variable {R}

theorem negCoord_def (k : ι) :
    negCoord R (Q := Q) k =
      piCongrRight (Function.update (fun i ↦ ContinuousLinearEquiv.refl R (Q i)) k (neg R)) :=
  (rfl)

/-- `negCoord` updates the `k`-th coordinate by its negation. -/
theorem negCoord_eq_update (k : ι) (x : (i : ι) → Q i) :
    negCoord R k x = Function.update x k (-x k) := by
  ext i
  by_cases h : i = k
  · subst h
    simp [negCoord]
  · simp [negCoord, h]

@[simp]
theorem negCoord_apply_same (k : ι) (x : (i : ι) → Q i) :
    negCoord R k x k = -x k := by
  simp [negCoord]

@[simp]
theorem negCoord_apply_of_ne {k i : ι} (h : i ≠ k) (x : (i : ι) → Q i) :
    negCoord R k x i = x i := by
  simp [negCoord, h]

@[simp]
theorem symm_negCoord (k : ι) :
    (negCoord R (Q := Q) k).symm = negCoord R k := by
  ext x i
  by_cases h : i = k
  · subst h
    simp [negCoord]
  · simp [negCoord, h]

@[simp]
theorem negCoord_negCoord (k : ι) (x : (i : ι) → Q i) :
    negCoord R k (negCoord R k x) = x := by
  ext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

@[simp]
theorem negCoord_single_same (k : ι) (v : Q k) :
    negCoord R (Q := Q) k (Pi.single k v) = Pi.single k (-v) := by
  simp [negCoord]

@[simp]
theorem negCoord_single_of_ne {k i : ι} (h : i ≠ k) (v : Q i) :
    negCoord R (Q := Q) k (Pi.single i v) = Pi.single i v := by
  simp [negCoord, h]

end NegCoord

end ContinuousLinearEquiv

namespace TauCeti

/-- Regrouping a family of tuples along a bijection of the sigma index, as a continuous linear
equivalence. The underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`. -/
def piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → E) ≃L[R] (ι' → E) where
  __ := piSigmaConstHomeomorph E e
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp

/-- The continuous linear regrouping has the existing regrouping homeomorphism as its function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (piSigmaConstContinuousLinearEquiv R E e : (∀ i, κ i → E) → (ι' → E)) =
      piSigmaConstHomeomorph E e :=
  (rfl)

/-- The inverse continuous linear regrouping has the inverse regrouping homeomorphism as its
function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((piSigmaConstContinuousLinearEquiv R E e).symm : (ι' → E) → ∀ i, κ i → E) =
      (piSigmaConstHomeomorph E e).symm :=
  (rfl)

end TauCeti
