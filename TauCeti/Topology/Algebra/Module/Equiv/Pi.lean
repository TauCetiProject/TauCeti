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

`TauCeti.piSigmaConstContinuousLinearEquiv` regroups a family of tuples along a bijection of its
sigma index. Its underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`, which is linear
coordinatewise, so coordinate calculations can use both the homeomorphism and the linear API.

Two naturality lemmas relate `ContinuousLinearMap.piMap` to regrouping:
`ContinuousLinearMap.consEquivL_symm_comp_piMap` splits a product operator over `Fin (n + 1)`
into the binary product of its first factor with the product of the remaining ones, and
`ContinuousLinearMap.piCongrLeft_symm_comp_piMap` reindexes a product operator along an
equivalence of index types.
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

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} [Semiring R]

section Fin

variable {n : ℕ} {E F : Fin (n + 1) → Type*}
variable [∀ i, AddCommMonoid (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommMonoid (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module R (F i)]

/-- Splitting off the first coordinate turns a product over `Fin (n + 1)` into the binary product
of its first factor with the product of the remaining ones. -/
theorem consEquivL_symm_comp_piMap (T : ∀ i, E i →L[R] F i) :
    ((Fin.consEquivL R F).symm : (∀ i, F i) →L[R] F 0 × ∀ i : Fin n, F i.succ) ∘L piMap T =
      ((T 0).prodMap (piMap fun i : Fin n ↦ T i.succ)) ∘L
        ((Fin.consEquivL R E).symm : (∀ i, E i) →L[R] E 0 × ∀ i : Fin n, E i.succ) := by
  ext x <;> simp [Fin.tail]

end Fin

section Reindex

variable {ι ι' : Type*} {E F : ι → Type*}
variable [∀ i, AddCommMonoid (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommMonoid (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module R (F i)]

/-- Reindexing a product operator along `e : ι' ≃ ι` gives the product of the reindexed family.

Mathlib has no evaluation lemmas for `ContinuousLinearEquiv.piCongrLeft`; its inverse is
`Equiv.piCongrLeft'`, which reads the coordinate `i'` at `e i'` by definition, so both sides
agree definitionally. -/
theorem piCongrLeft_symm_comp_piMap (e : ι' ≃ ι) (T : ∀ i, E i →L[R] F i) :
    ((ContinuousLinearEquiv.piCongrLeft R F e).symm : (∀ i, F i) →L[R] ∀ i', F (e i')) ∘L
        piMap T =
      piMap (fun i' ↦ T (e i')) ∘L
        ((ContinuousLinearEquiv.piCongrLeft R E e).symm : (∀ i, E i) →L[R] ∀ i', E (e i')) :=
  (rfl)

end Reindex

end ContinuousLinearMap

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
