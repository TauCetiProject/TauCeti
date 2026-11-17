/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Topology.PiCurry

/-!
# Continuous linear regrouping of coordinate families

`ContinuousLinearEquiv.piOptionEquivProd` splits a dependent family indexed by `Option ι`
into its `none` coordinate and its `some` coordinates, and
`ContinuousLinearEquiv.piProdEquivPiOption` reassembles a family on `ι` paired with a
distinguished coordinate into a family on `Option ι`. Both supply product coordinates
for linear charts, with no finiteness or norm assumptions.

The construction combines `LinearEquiv.piOptionEquivProd` with
`TauCeti.piOptionEquivProdHomeomorph`.

For Mathlib's `ContinuousLinearEquiv.sumPiEquivProdPi`, which splits a family indexed by `S ⊕ T`
into its restrictions to `S` and to `T`, `ContinuousLinearEquiv.sumPiEquivProdPi_apply` and
`ContinuousLinearEquiv.sumPiEquivProdPi_symm_apply` evaluate the equivalence and its inverse, and
`ContinuousLinearEquiv.piProdEquivPiSumUnique` identifies `(σ → M) × M` with `σ ⊕ τ → M` for any
unique index type `τ`.

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

/-- Identify a family indexed by `ι` paired with a distinguished coordinate as a family indexed by
`Option ι`, placing the distinguished coordinate at `none`. -/
def piProdEquivPiOption :
    (((i : ι) → M (some i)) × M none) ≃L[R] ((i : Option ι) → M i) :=
  (prodComm R ((i : ι) → M (some i)) (M none)).trans (piOptionEquivProd R).symm

/-- Applying `piProdEquivPiOption` places the distinguished coordinate at `none` and the remaining
coordinates at `some i`. -/
@[simp] theorem piProdEquivPiOption_apply (q : ((i : ι) → M (some i)) × M none) :
    piProdEquivPiOption R q = (fun i => match i with
      | none => q.2
      | some j => q.1 j) := by
  funext i
  cases i <;> rfl

/-- The inverse of `piProdEquivPiOption` extracts the `some` coordinates and the `none`
coordinate. -/
@[simp] theorem piProdEquivPiOption_symm_apply (x : (i : Option ι) → M i) :
    (piProdEquivPiOption R).symm x = (fun i => x (some i), x none) := (rfl)

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

/-- Identify a family indexed by `σ` paired with a single value in `N` as a family indexed by
`σ ⊕ τ` for any unique index type `τ`. -/
def piProdEquivPiSumUnique (σ τ N : Type*) [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] :
    ((σ → N) × N) ≃L[R] (σ ⊕ τ → N) :=
  ((ContinuousLinearEquiv.refl R (σ → N)).prodCongr (funUnique τ R N).symm).trans
    (sumPiEquivProdPi R σ τ (fun _ ↦ N)).symm

/-- Applying `piProdEquivPiSumUnique` combines the `σ`-indexed family with the constant value on
`τ` via `Sum.elim`. -/
@[simp] theorem piProdEquivPiSumUnique_apply {σ τ N : Type*} [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] (q : (σ → N) × N) :
    piProdEquivPiSumUnique R σ τ N q = Sum.elim q.1 (fun _ ↦ q.2) := by
  funext x
  cases x <;> rfl

/-- The inverse of `piProdEquivPiSumUnique` restricts to `σ` and evaluates at `Sum.inr default`. -/
@[simp] theorem piProdEquivPiSumUnique_symm_apply {σ τ N : Type*} [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] (p : σ ⊕ τ → N) :
    (piProdEquivPiSumUnique R σ τ N).symm p = (p ∘ Sum.inl, p (.inr default)) :=
  (rfl)

end SumPi

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
