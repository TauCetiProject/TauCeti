/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# An isotypic component is its type tensored with its multiplicity space

Let `A` be an algebra over a field `k` and let `S` be a simple `A`-module.  For any `A`-module `M`
the **multiplicity space** of `S` in `M` is the hom space `S →ₗ[A] M`, a `k`-module whose dimension
is the multiplicity of `S` in `M`
(`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`).  Evaluation

`TauCeti.isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`,

is `A`-linear for the action on the left factor alone, and this file proves that it is an
isomorphism onto the `S`-isotypic component of `M`:

`S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.

This is the *uncounted* form of the isotypic decomposition.  The counted form is already available
— `TauCeti.nonempty_linearEquiv_isotypicComponent` writes the component as `S ^ m` with
`m = finrank k (S →ₗ[A] M)` — but only up to a choice of isomorphism, so it destroys any structure
the multiplicity space carries.  The tensor form keeps it: every endomorphism of `M` commuting with
`A` acts on the second factor and on nothing else (`TauCeti.isotypicEval_comp`), which is exactly
what a double-centralizer decomposition consumes.

## The range, and then the dimensions

Identifying the range needs no finiteness and no algebraically closed field: a map out of a simple
module has simple or zero range, so it lands in the isotypic component
(`TauCeti.apply_mem_isotypicComponent`), and conversely each submodule `m ≅ S` is the range of one
such map, so the two inclusions give `TauCeti.range_isotypicEval`.

Injectivity is where the hypotheses enter, and it is proved by counting rather than by hand: over
an algebraically closed field the multiplicity theorem gives
`finrank (isotypicComponent A M S) = finrank (S →ₗ[A] M) · finrank S`
(`TauCeti.finrank_isotypicComponent`), which is the dimension of the tensor product, so a
surjection between them is bijective.  A direct argument would have to produce a basis of the
multiplicity space and show that the corresponding submodules are independent, which is the same
count in disguise.

## Main definitions

* `TauCeti.isotypicEval`: **evaluation** `S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`.
* `TauCeti.isotypicComponentTensorEquiv`: **the isotypic component is `S` tensored with its
  multiplicity space**, `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.
* `TauCeti.isotypicTensorEquiv`: the same for a module that is its own isotypic component,
  `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`, and `TauCeti.isIsotypicOfTypeTensorEquiv`, its form for a
  semisimple module whose isotypy is given as `IsIsotypicOfType`.

## Main results

* `TauCeti.range_isotypicEval`: **the range of evaluation is the isotypic component.**
* `TauCeti.isotypicEval_comp`: **naturality** — postcomposing with an `A`-linear map `M → N` is
  evaluation of the map it induces on multiplicity spaces, so a commuting operator acts on the
  multiplicity space only.
* `TauCeti.isotypicEval_injective`: evaluation is injective.
* `TauCeti.isotypicTensorEquiv_map` and `TauCeti.isotypicTensorEquiv_symm_apply_map`: the
  naturality above, read on the equivalence and on its inverse — the form that transports the
  commutant of `A` onto the multiplicity space.

## References

This is the isotypic decomposition in the form asked for by Layer 8 of
`TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md`, *"the isotypic decomposition
`(kⁿ)^{⊗d} ≅ ⊕_μ S^μ ⊗ Hom_{S_d}(S^μ, (kⁿ)^{⊗d})` of a representation of the semisimple algebra
`k[S_d]`"*, which is the half of the Schur-functor decomposition that
`TauCeti/RepresentationTheory/ClassicalGroups/WeylModule/Multiplicity.lean` does not supply.

* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §25.
* J.-P. Serre, *Linear Representations of Finite Groups*, §2.6.
-/

public section

namespace TauCeti

open Module TensorProduct

variable (k : Type*) {A S M N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup S] [Module k S] [Module A S] [IsScalarTower k A S]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-! ### Evaluation -/

/-- Evaluation of a multiplicity space at a vector, curried.  It is `A`-linear in the vector
because an `A`-linear map commutes with the action of `A`, and `k`-linear in the map because the
`k`-action on a hom space is pointwise. -/
private def isotypicEvalAux : S →ₗ[A] (S →ₗ[A] M) →ₗ[k] M where
  toFun s :=
    { toFun := fun f ↦ f s
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_add' s t := by ext f; exact f.map_add s t
  map_smul' a s := by ext f; exact f.map_smul a s

/-- **Evaluation** `S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`.  Only the left factor carries an
`A`-action, so this is a map of `A`-modules for the `TensorProduct.leftModule` structure. -/
def isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M :=
  AlgebraTensorModule.lift (isotypicEvalAux k)

@[simp]
theorem isotypicEval_tmul (s : S) (f : S →ₗ[A] M) : isotypicEval k (s ⊗ₜ f) = f s :=
  (rfl)

/-- **Naturality of evaluation in the target.**  Postcomposition with an `A`-linear map
`g : M →ₗ[A] N` is, on the tensor factorization, the map `g` induces on multiplicity spaces; the
left factor is untouched.  So an operator commuting with `A` acts through the multiplicity space
alone, which is what makes the second factor a module over the commutant. -/
theorem isotypicEval_comp (g : M →ₗ[A] N) :
    g ∘ₗ isotypicEval k (S := S) =
      isotypicEval k ∘ₗ
        AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) := by
  refine AlgebraTensorModule.curry_injective ?_
  ext s f
  rfl

/-- The value form of `TauCeti.isotypicEval_comp`. -/
theorem isotypicEval_map_apply (g : M →ₗ[A] N) (x : S ⊗[k] (S →ₗ[A] M)) :
    isotypicEval k
        (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) x) = g (isotypicEval k x) :=
  (LinearMap.congr_fun (isotypicEval_comp k g) x).symm

/-! ### The range is the isotypic component -/

variable [IsSimpleModule A S]

/-- **The range of evaluation is the `S`-isotypic component of `M`.**  A map out of `S` lands in
the component, and every submodule of `M` isomorphic to `S` is the range of such a map.  No
finiteness and no hypothesis on `k` beyond being a field are used. -/
theorem range_isotypicEval :
    LinearMap.range (isotypicEval k (S := S) (M := M)) = isotypicComponent A M S := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    induction x using TensorProduct.inductionOn with
    | tmul s f => simpa using apply_mem_isotypicComponent f s
    | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  · refine sSup_le ?_
    rintro m ⟨e⟩ x hx
    refine ⟨e ⟨x, hx⟩ ⊗ₜ (m.subtype ∘ₗ (e.symm : S →ₗ[A] m)), ?_⟩
    simp

/-! ### The tensor decomposition of an isotypic component -/

variable [IsAlgClosed k] [FiniteDimensional k S] [FiniteDimensional k M]

/-- Evaluation, corestricted to the isotypic component it surjects onto. -/
private def isotypicEvalCodRestrict :
    S ⊗[k] (S →ₗ[A] M) →ₗ[A] isotypicComponent A M S :=
  (isotypicEval k).codRestrict _ fun x ↦ by
    rw [← range_isotypicEval k]; exact LinearMap.mem_range_self _ x

private theorem finrank_tensor_eq_finrank_isotypicComponent :
    finrank k (S ⊗[k] (S →ₗ[A] M)) = finrank k (isotypicComponent A M S) := by
  rw [Module.finrank_tensorProduct, finrank_isotypicComponent (k := k), mul_comm]

private theorem isotypicEvalCodRestrict_bijective :
    Function.Bijective (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)) := by
  have hsurj : Function.Surjective (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)) := by
    rintro ⟨y, hy⟩
    rw [← range_isotypicEval k] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨?_, hsurj⟩
  have : FiniteDimensional k (isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)).restrictScalars k)
    (finrank_tensor_eq_finrank_isotypicComponent k)).2 hsurj

/-- **An isotypic component is its type tensored with its multiplicity space.**  Evaluation
`s ⊗ f ↦ f s` is an isomorphism of `A`-modules from `S ⊗[k] (S →ₗ[A] M)` onto the `S`-isotypic
component of `M`.  The `A`-action is on the left factor only, so the multiplicity space carries
whatever commutes with `A`. -/
noncomputable def isotypicComponentTensorEquiv :
    S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S :=
  .ofBijective _ (isotypicEvalCodRestrict_bijective k (A := A) (S := S) (M := M))

@[simp]
theorem isotypicComponentTensorEquiv_apply_coe (x : S ⊗[k] (S →ₗ[A] M)) :
    (isotypicComponentTensorEquiv k x : M) = isotypicEval k x :=
  (rfl)

/-- **Evaluation is injective.** -/
theorem isotypicEval_injective :
    Function.Injective (isotypicEval k (A := A) (S := S) (M := M)) := fun _ _ h ↦
  (isotypicComponentTensorEquiv k (A := A) (S := S) (M := M)).injective (Subtype.ext h)

/-- **A module that is its own `S`-isotypic component is `S` tensored with its multiplicity
space.**  For a semisimple `M` the hypothesis is `IsIsotypicOfType A M S`, through
`isotypicComponent_eq_top_iff`. -/
noncomputable def isotypicTensorEquiv (h : isotypicComponent A M S = ⊤) :
    S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M :=
  (isotypicComponentTensorEquiv k (A := A) (S := S) (M := M)).trans (LinearEquiv.ofTop _ h)

@[simp]
theorem isotypicTensorEquiv_apply (h : isotypicComponent A M S = ⊤)
    (x : S ⊗[k] (S →ₗ[A] M)) : isotypicTensorEquiv k h x = isotypicEval k x :=
  (rfl)

/-- **An isotypic semisimple module is `S` tensored with its multiplicity space.**  This is
`TauCeti.isotypicTensorEquiv` with the hypothesis in the form `IsIsotypicOfType`: for a semisimple
module the two are the same, by `isotypicComponent_eq_top_iff`. -/
noncomputable def isIsotypicOfTypeTensorEquiv [IsSemisimpleModule A M]
    (h : IsIsotypicOfType A M S) : S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M :=
  isotypicTensorEquiv k (isotypicComponent_eq_top_iff.mpr h)

@[simp]
theorem isIsotypicOfTypeTensorEquiv_apply [IsSemisimpleModule A M] (h : IsIsotypicOfType A M S)
    (x : S ⊗[k] (S →ₗ[A] M)) : isIsotypicOfTypeTensorEquiv k h x = isotypicEval k x :=
  isotypicTensorEquiv_apply k _ x

/-- **The tensor decomposition is natural in the target.**  An `A`-linear endomorphism of `M` acts
on the multiplicity space alone: this is `TauCeti.isotypicEval_comp` read through the
equivalence. -/
theorem isotypicTensorEquiv_map (h : isotypicComponent A M S = ⊤) (g : M →ₗ[A] M)
    (x : S ⊗[k] (S →ₗ[A] M)) :
    isotypicTensorEquiv k h
        (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) x) = g (isotypicTensorEquiv k h x) := by
  rw [isotypicTensorEquiv_apply, isotypicTensorEquiv_apply, isotypicEval_map_apply]

/-- **Transporting a commuting operator to the multiplicity space.**  Reading
`TauCeti.isotypicTensorEquiv_map` backwards: the inverse equivalence carries an `A`-linear
endomorphism `g` of `M` to `1 ⊗ (g ∘ ·)`, so under the decomposition the commutant of `A` in
`Module.End k M` acts on the multiplicity space and trivially on `S`. -/
theorem isotypicTensorEquiv_symm_apply_map (h : isotypicComponent A M S = ⊤) (g : M →ₗ[A] M)
    (y : M) :
    (isotypicTensorEquiv k h).symm (g y) =
      AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
        (LinearMap.compRight (M := S) k g) ((isotypicTensorEquiv k h).symm y) := by
  apply (isotypicTensorEquiv k h).injective
  rw [LinearEquiv.apply_symm_apply, isotypicTensorEquiv_map, LinearEquiv.apply_symm_apply]

end TauCeti
