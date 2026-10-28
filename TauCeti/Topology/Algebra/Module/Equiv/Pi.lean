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
sigma index. It combines Mathlib's linear currying and reindexing with the topology of
`TauCeti.piSigmaConstHomeomorph`, so coordinate calculations can use both APIs.
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

private theorem coe_piCurry_symm_trans_piCongrLeft_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((LinearEquiv.piCurry R (fun _ _ => E)).symm.trans
      (LinearEquiv.piCongrLeft R (fun _ : Sigma κ => E) e.symm).symm :
        (∀ i, κ i → E) → (ι' → E)) = piSigmaConstHomeomorph E e := by
  ext x j
  simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrLeft, LinearEquiv.symm_symm,
    Equiv.symm_symm, LinearEquiv.piCongrLeft'_apply, LinearEquiv.piCurry_symm_apply,
    piSigmaConstHomeomorph_apply, Sigma.uncurry]

/-- Regrouping a family of tuples along a bijection of the sigma index, as a continuous linear
equivalence. The underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`. -/
def piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → E) ≃L[R] (ι' → E) where
  toLinearEquiv := (LinearEquiv.piCurry R (fun _ _ => E)).symm.trans
    (LinearEquiv.piCongrLeft R (fun _ : Sigma κ => E) e.symm).symm
  continuous_toFun := by
    rw [LinearMap.toFun_eq_coe, LinearEquiv.coe_toLinearMap,
      coe_piCurry_symm_trans_piCongrLeft_symm]
    exact (piSigmaConstHomeomorph E e).continuous
  continuous_invFun := (piSigmaConstHomeomorph E e).symm.continuous.congr fun x => by
    rw [LinearEquiv.invFun_eq_symm]
    apply ((LinearEquiv.piCurry R (fun _ _ => E)).symm.trans
      (LinearEquiv.piCongrLeft R (fun _ : Sigma κ => E) e.symm).symm).injective
    rw [LinearEquiv.apply_symm_apply, coe_piCurry_symm_trans_piCongrLeft_symm,
      Homeomorph.apply_symm_apply]

/-- The continuous linear regrouping has the existing regrouping homeomorphism as its function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (piSigmaConstContinuousLinearEquiv R E e : (∀ i, κ i → E) → (ι' → E)) =
      piSigmaConstHomeomorph E e := by
  simpa only [piSigmaConstContinuousLinearEquiv, ContinuousLinearEquiv.coe_mk] using
    coe_piCurry_symm_trans_piCongrLeft_symm R E e

/-- The inverse continuous linear regrouping has the inverse regrouping homeomorphism as its
function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((piSigmaConstContinuousLinearEquiv R E e).symm : (ι' → E) → ∀ i, κ i → E) =
      (piSigmaConstHomeomorph E e).symm := by
  funext x
  apply (piSigmaConstContinuousLinearEquiv R E e).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, coe_piSigmaConstContinuousLinearEquiv,
    Homeomorph.apply_symm_apply]

end TauCeti
