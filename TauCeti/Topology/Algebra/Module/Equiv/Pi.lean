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
