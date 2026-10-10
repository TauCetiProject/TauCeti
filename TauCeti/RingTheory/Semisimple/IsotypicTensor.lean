/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import TauCeti.RingTheory.Semisimple.Multiplicity
-- Non-public: the rank criterion for a self-map to be injective is used only inside the proof of
-- injectivity on a finite-dimensional target; no exported statement mentions a dimension.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An isotypic component is its type tensored with its multiplicity space

Let `A` be an algebra over a field `k` and let `S` be a simple `A`-module.  For any `A`-module `M`
the **multiplicity space** of `S` in `M` is the hom space `S →ₗ[A] M`; when `k` is algebraically
closed and `S` is finite-dimensional its dimension is the multiplicity of `S` in `M`
(`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`).  Evaluation

`TauCeti.isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`,

is `A`-linear for the action on the left factor alone, and has the `S`-isotypic component of `M`
as its range (`TauCeti.range_isotypicEval`).  This file proves that it is injective, so that

`S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.

Injectivity asks that `S` be simple and finite-dimensional over an algebraically closed `k`, and
nothing at all of `M`.

This is the *uncounted* form of the isotypic decomposition.  The counted form is already available
— `TauCeti.nonempty_linearEquiv_isotypicComponent` writes the component as `S ^ m` with
`m = finrank k (S →ₗ[A] M)` — but only up to a choice of isomorphism, so it destroys any structure
the multiplicity space carries.  The tensor form keeps it: every endomorphism of `M` commuting with
`A` acts on the second factor and on nothing else (`TauCeti.isotypicEval_comp`), which is exactly
what a double-centralizer decomposition consumes.

## Main definitions

* `TauCeti.isotypicComponentTensorEquiv`: **the isotypic component is `S` tensored with its
  multiplicity space**, `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.
* `TauCeti.isotypicTensorEquiv`: the same for a module that is its own isotypic component,
  `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`.

## Main results

* `TauCeti.isotypicEval_injective`: **evaluation is injective**, for `S` simple and
  finite-dimensional over an algebraically closed `k`, with no finiteness asked of the target.
* `TauCeti.isotypicComponentTensorEquiv_map_coe` and `TauCeti.isotypicTensorEquiv_map`:
  **naturality in the target** — an `A`-linear map acts on the multiplicity space and on nothing
  else, read on the equivalences.
* `TauCeti.isotypicTensorEquiv_symm_apply_map`: the same read on the inverse — the form that
  transports the commutant of `A` onto the multiplicity space.

## References

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
variable [IsSimpleModule A S] [IsAlgClosed k] [FiniteDimensional k S]

/-! ### Injectivity of evaluation -/

/-- Evaluation, corestricted to the isotypic component it surjects onto. -/
private def isotypicEvalCodRestrict :
    S ⊗[k] (S →ₗ[A] M) →ₗ[A] isotypicComponent A M S :=
  (isotypicEval k).codRestrict _ fun x ↦ by
    rw [← range_isotypicEval k]; exact LinearMap.mem_range_self _ x

omit [IsAlgClosed k] [FiniteDimensional k S] in
private theorem isotypicEvalCodRestrict_surjective :
    Function.Surjective (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)) := by
  rintro ⟨y, hy⟩
  rw [← range_isotypicEval k] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem finrank_tensor_eq_finrank_isotypicComponent [FiniteDimensional k M] :
    finrank k (S ⊗[k] (S →ₗ[A] M)) = finrank k (isotypicComponent A M S) := by
  rw [Module.finrank_tensorProduct, finrank_isotypicComponent (k := k), mul_comm]

/-- Evaluation is injective on a finite-dimensional target: it is onto the isotypic component,
and the two have the same dimension by the multiplicity theorem.  The general case reduces to
this one. -/
private theorem isotypicEval_injective_of_finiteDimensional [FiniteDimensional k M] :
    Function.Injective (isotypicEval k (A := A) (S := S) (M := M)) := by
  have : FiniteDimensional k (isotypicComponent A M S) :=
    .of_injective ((isotypicComponent A M S).subtype.restrictScalars k) Subtype.val_injective
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)).restrictScalars k)
    (finrank_tensor_eq_finrank_isotypicComponent k)).2
      (isotypicEvalCodRestrict_surjective k (A := A) (S := S) (M := M))
  exact fun _ _ h ↦ hinj (Subtype.ext h)

/-- **Evaluation is injective.**  Only `S` is asked to be simple and finite-dimensional over the
algebraically closed field `k`; the target `M` is arbitrary. -/
theorem isotypicEval_injective :
    Function.Injective (isotypicEval k (A := A) (S := S) (M := M)) := by
  classical
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨t, rfl⟩ := TensorProduct.exists_finset x
  -- Collect the ranges of the maps occurring in the sum into one finite-dimensional submodule.
  obtain ⟨F, hF⟩ : ∃ F : (t → S) →ₗ[A] M,
      ∀ (p : t) (s : S), F (Pi.single p s) = (p : S × (S →ₗ[A] M)).2 s :=
    ⟨∑ p : t, (p : S × (S →ₗ[A] M)).2 ∘ₗ LinearMap.proj p, fun p s ↦ by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single p (fun q _ hq ↦ by simp [Pi.single_eq_of_ne hq])
        fun h ↦ absurd (Finset.mem_univ p) h]
      simp⟩
  have hFD : FiniteDimensional k (LinearMap.range F) :=
    Module.Finite.of_surjective (F.rangeRestrict.restrictScalars k) F.surjective_rangeRestrict
  have hmem : ∀ (p : t) (s : S), (p : S × (S →ₗ[A] M)).2 s ∈ LinearMap.range F :=
    fun p s ↦ ⟨Pi.single p s, hF p s⟩
  -- Over that submodule the sum vanishes, hence is zero by the finite-dimensional case.
  have hzero : ∑ p : t, (p : S × (S →ₗ[A] M)).1 ⊗ₜ[k]
      ((p : S × (S →ₗ[A] M)).2.codRestrict (LinearMap.range F) (hmem p)) = 0 := by
    refine (injective_iff_map_eq_zero _).mp
      (isotypicEval_injective_of_finiteDimensional k (A := A) (S := S)
        (M := LinearMap.range F)) _ ?_
    rw [← Submodule.coe_eq_zero]
    simp only [map_sum, isotypicEval_tmul, Submodule.coe_sum, LinearMap.codRestrict_apply]
    rw [Finset.sum_coe_sort t fun q : S × (S →ₗ[A] M) ↦ q.2 q.1]
    simpa using hx
  -- Pushing back along the inclusion recovers the original sum.
  have := congrArg (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
    (LinearMap.compRight (M := S) k (LinearMap.range F).subtype)) hzero
  rw [← Finset.sum_coe_sort t fun q : S × (S →ₗ[A] M) ↦ q.1 ⊗ₜ[k] q.2]
  simpa using this

private theorem isotypicEvalCodRestrict_bijective :
    Function.Bijective (isotypicEvalCodRestrict k (A := A) (S := S) (M := M)) :=
  ⟨fun _ _ h ↦ isotypicEval_injective k (congrArg Subtype.val h),
    isotypicEvalCodRestrict_surjective k⟩

/-! ### The tensor decomposition -/

/-- **An isotypic component is its type tensored with its multiplicity space.**  Evaluation
`s ⊗ f ↦ f s` is an isomorphism of `A`-modules from `S ⊗[k] (S →ₗ[A] M)` onto the `S`-isotypic
component of `M`.  The `A`-action is on the left factor only, so the multiplicity space carries
whatever commutes with `A`. -/
noncomputable def isotypicComponentTensorEquiv :
    S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S :=
  .ofBijective _ (isotypicEvalCodRestrict_bijective k (A := A) (S := S) (M := M))

@[simp]
theorem isotypicComponentTensorEquiv_apply_coe (x : S ⊗[k] (S →ₗ[A] M)) :
    (isotypicComponentTensorEquiv k x : M) = isotypicEval k x := by
  rw [isotypicComponentTensorEquiv, LinearEquiv.ofBijective_apply, isotypicEvalCodRestrict,
    LinearMap.codRestrict_apply]

/-- **The component decomposition is natural in the target.**  An `A`-linear map `g : M →ₗ[A] N`
carries the `S`-isotypic component of `M` into that of `N`, and through the equivalences it is the
map `g` induces on multiplicity spaces: it acts on the second factor and on nothing else. -/
theorem isotypicComponentTensorEquiv_map_coe (g : M →ₗ[A] N) (x : S ⊗[k] (S →ₗ[A] M)) :
    (isotypicComponentTensorEquiv k (M := N)
        (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) x) : N) =
      g (isotypicComponentTensorEquiv k x : M) := by
  rw [isotypicComponentTensorEquiv_apply_coe, isotypicComponentTensorEquiv_apply_coe,
    isotypicEval_map_apply]

/-- **A module that is its own `S`-isotypic component is `S` tensored with its multiplicity
space.**  For a semisimple `M` the hypothesis is `IsIsotypicOfType A M S`, through
`isotypicComponent_eq_top_iff`. -/
noncomputable def isotypicTensorEquiv (h : isotypicComponent A M S = ⊤) :
    S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M :=
  (isotypicComponentTensorEquiv k (A := A) (S := S) (M := M)).trans (LinearEquiv.ofTop _ h)

@[simp]
theorem isotypicTensorEquiv_apply (h : isotypicComponent A M S = ⊤)
    (x : S ⊗[k] (S →ₗ[A] M)) : isotypicTensorEquiv k h x = isotypicEval k x := by
  rw [isotypicTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.ofTop_apply,
    isotypicComponentTensorEquiv_apply_coe]

-- Not `@[simp]`: `isotypicTensorEquiv_apply` already rewrites the left-hand side, after which
-- `isotypicEval_map_apply` finishes, so tagging this lemma would leave it outside simp normal
-- form.
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
@[simp]
theorem isotypicTensorEquiv_symm_apply_map (h : isotypicComponent A M S = ⊤) (g : M →ₗ[A] M)
    (y : M) :
    (isotypicTensorEquiv k h).symm (g y) =
      AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
        (LinearMap.compRight (M := S) k g) ((isotypicTensorEquiv k h).symm y) := by
  apply (isotypicTensorEquiv k h).injective
  rw [LinearEquiv.apply_symm_apply, isotypicTensorEquiv_map, LinearEquiv.apply_symm_apply]

end TauCeti
