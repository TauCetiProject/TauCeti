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
the **multiplicity space** of `S` in `M` is the hom space `S →ₗ[A] M`.  Its dimension deserves the
name: when `k` is algebraically closed, `S` is finite-dimensional and `M` is a finite product of
simple modules, that dimension is the number of factors of `M` isomorphic to `S`
(`TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`).  Evaluation

`TauCeti.isotypicEval : S ⊗[k] (S →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`,

is `A`-linear for the action on the left factor alone, and has the `S`-isotypic component of `M`
as its range (`TauCeti.range_isotypicEval`).  This file proves that it is injective, so that

`S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.

Injectivity asks that `S` be simple and finite-dimensional over an algebraically closed `k`, and
nothing at all of `M`.

This is the *uncounted* form of the isotypic decomposition.  A counted form is already available
— `TauCeti.nonempty_linearEquiv_isotypicComponent` writes the component as `S ^ m` with
`m = finrank k (S →ₗ[A] M)` — but it asks `M` itself to be finite-dimensional over `k`, and it
produces only an unspecified isomorphism, so it destroys any structure the multiplicity space
carries.  The tensor form asks nothing of `M` and keeps that structure: every `A`-linear map out
of `M` acts on the second factor and on nothing else (`TauCeti.isotypicEval_comp`), which is
exactly what a double-centralizer decomposition consumes.

Summing over components gives the uncounted form of the whole decomposition of a semisimple
module. For pairwise non-isomorphic simple modules `S j` that represent every simple submodule of a
semisimple `M`, evaluation is an isomorphism `⨁ⱼ S j ⊗[k] (S j →ₗ[A] M) ≃ₗ[A] M`. Injectivity
combines injectivity on each summand with the independence of the isotypic components
(`TauCeti.iSupIndep_isotypicComponent`). Again nothing is asked of `M` beyond semisimplicity; in
particular infinitely many `S j` may occur, with infinite-dimensional multiplicity spaces.

## Main definitions

* `TauCeti.isotypicComponentTensorEquiv`: **the isotypic component is `S` tensored with its
  multiplicity space**, `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] isotypicComponent A M S`.
* `TauCeti.isotypicTensorEquiv`: the same for a module that is its own isotypic component,
  `S ⊗[k] (S →ₗ[A] M) ≃ₗ[A] M`.
* `TauCeti.directSumIsotypicEval`: the sum of the evaluation maps of a family of modules `S j`.
* `TauCeti.directSumIsotypicTensorEquiv`: **the isotypic decomposition of a semisimple module**,
  `⨁ⱼ S j ⊗[k] (S j →ₗ[A] M) ≃ₗ[A] M`.

## Main results

* `TauCeti.isotypicEval_injective`: **evaluation is injective**, for `S` simple and
  finite-dimensional over an algebraically closed `k`, with no finiteness asked of the target.
* `TauCeti.isotypicComponentTensorEquiv_map_coe` and `TauCeti.isotypicTensorEquiv_map`:
  **naturality in the target** — an `A`-linear map `M →ₗ[A] N` acts on the multiplicity space and
  on nothing else, read on the equivalences.
* `TauCeti.isotypicTensorEquiv_symm_apply_map`: the same read on the inverse — the form that,
  taking `N = M`, transports the commutant of `A` onto the multiplicity space.
* `TauCeti.range_directSumIsotypicEval`: the range of the summed evaluation is the sum of the
  isotypic components; `TauCeti.directSumIsotypicEval_surjective` and
  `TauCeti.directSumIsotypicEval_injective` give the two halves of the decomposition.
* `TauCeti.directSumIsotypicEval_comp`, `TauCeti.directSumIsotypicTensorEquiv_map` and
  `TauCeti.directSumIsotypicTensorEquiv_symm_apply_map`: naturality of the decomposition in the
  target, so that `A`-linear maps act on the multiplicity spaces alone.

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
/-- **The tensor decomposition is natural in the target.**  For `M` and `N` both their own
`S`-isotypic components, an `A`-linear map `g : M →ₗ[A] N` acts on the multiplicity space alone:
this is `TauCeti.isotypicEval_comp` read through the equivalences. -/
theorem isotypicTensorEquiv_map (hM : isotypicComponent A M S = ⊤)
    (hN : isotypicComponent A N S = ⊤) (g : M →ₗ[A] N) (x : S ⊗[k] (S →ₗ[A] M)) :
    isotypicTensorEquiv k hN
        (AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
          (LinearMap.compRight (M := S) k g) x) = g (isotypicTensorEquiv k hM x) := by
  rw [isotypicTensorEquiv_apply, isotypicTensorEquiv_apply, isotypicEval_map_apply]

/-- **Transporting a map to the multiplicity space.**  Reading
`TauCeti.isotypicTensorEquiv_map` backwards: the inverse equivalences carry an `A`-linear map
`g : M →ₗ[A] N` to `1 ⊗ (g ∘ ·)`.  For `N = M` this says that under the decomposition the
commutant of `A` in `Module.End k M` acts on the multiplicity space and trivially on `S`. -/
@[simp]
theorem isotypicTensorEquiv_symm_apply_map (hM : isotypicComponent A M S = ⊤)
    (hN : isotypicComponent A N S = ⊤) (g : M →ₗ[A] N) (y : M) :
    (isotypicTensorEquiv k hN).symm (g y) =
      AlgebraTensorModule.map (LinearMap.id (R := A) (M := S))
        (LinearMap.compRight (M := S) k g) ((isotypicTensorEquiv k hM).symm y) := by
  apply (isotypicTensorEquiv k hN).injective
  rw [LinearEquiv.apply_symm_apply, isotypicTensorEquiv_map k hM hN, LinearEquiv.apply_symm_apply]

end TauCeti

/-! ### The isotypic decomposition of a semisimple module -/

namespace TauCeti

open TensorProduct

section DirectSum

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
  {κ : Type*} [DecidableEq κ] (S : κ → Type*) [∀ j, AddCommGroup (S j)] [∀ j, Module k (S j)]
  [∀ j, Module A (S j)] [∀ j, IsScalarTower k A (S j)]
  (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The sum over a family of modules `S j` of the evaluation maps
`S j ⊗[k] (S j →ₗ[A] M) →ₗ[A] M`, `s ⊗ f ↦ f s`. -/
noncomputable def directSumIsotypicEval : (Π₀ j, S j ⊗[k] (S j →ₗ[A] M)) →ₗ[A] M :=
  DFinsupp.lsum ℕ fun _ => isotypicEval k

/-- On the `j`-th summand, `directSumIsotypicEval` is the evaluation map of `S j`. -/
@[simp]
theorem directSumIsotypicEval_single (j : κ) (x : S j ⊗[k] (S j →ₗ[A] M)) :
    directSumIsotypicEval k A S M (DFinsupp.single j x) = isotypicEval k x :=
  DFinsupp.lsum_single _ _ _ _

/-- `directSumIsotypicEval` factors through the direct sum of the ranges of the summands. -/
private theorem directSumIsotypicEval_eq_lsum_comp :
    directSumIsotypicEval k A S M =
      (DFinsupp.lsum ℕ fun j => (LinearMap.range (isotypicEval k (S := S j) (M := M))).subtype)
        ∘ₗ DFinsupp.mapRange.linearMap fun _ => (isotypicEval k).rangeRestrict := by
  ext j x
  simp

section Naturality

variable {A M} {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- **Naturality of the summed evaluation in the target.** An `A`-linear map `g : M →ₗ[A] N`
acts on each summand through its multiplicity space alone; the factors `S j` are untouched. -/
theorem directSumIsotypicEval_comp (g : M →ₗ[A] N) :
    g ∘ₗ directSumIsotypicEval k A S M =
      directSumIsotypicEval k A S N ∘ₗ DFinsupp.mapRange.linearMap fun j =>
        AlgebraTensorModule.map (LinearMap.id (R := A) (M := S j))
          (LinearMap.compRight (M := S j) k g) := by
  ext j x
  simp

-- Not `@[simp]`, unlike `TauCeti.isotypicEval_map_apply`: the `simps` lemma
-- `DFinsupp.mapRange.linearMap_apply` already rewrites the left-hand side.
/-- The value form of `TauCeti.directSumIsotypicEval_comp`. -/
theorem directSumIsotypicEval_map_apply (g : M →ₗ[A] N) (x : Π₀ j, S j ⊗[k] (S j →ₗ[A] M)) :
    directSumIsotypicEval k A S N
        (DFinsupp.mapRange.linearMap (fun j =>
          AlgebraTensorModule.map (LinearMap.id (R := A) (M := S j))
            (LinearMap.compRight (M := S j) k g)) x) =
      g (directSumIsotypicEval k A S M x) :=
  (LinearMap.congr_fun (directSumIsotypicEval_comp k S g) x).symm

end Naturality

variable [∀ j, IsSimpleModule A (S j)]

/-- The range of `directSumIsotypicEval` is the sum of the isotypic components of the `S j`. -/
theorem range_directSumIsotypicEval :
    LinearMap.range (directSumIsotypicEval k A S M) = ⨆ j, isotypicComponent A M (S j) := by
  rw [directSumIsotypicEval_eq_lsum_comp, LinearMap.range_comp_of_range_eq_top,
    ← Submodule.iSup_eq_range_dfinsupp_lsum]
  · simp only [range_isotypicEval]
  · exact LinearMap.range_eq_top.mpr <|
      (DFinsupp.mapRange_surjective _ fun _ => map_zero _).mpr fun _ =>
        LinearMap.surjective_rangeRestrict _

variable {A M}

/-- Evaluation is onto a semisimple module `M` as soon as each simple submodule of `M` is
isomorphic to one of the `S j`. -/
theorem directSumIsotypicEval_surjective [IsSemisimpleModule A M]
    (hcover : ∀ m : Submodule A M, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m)) :
    Function.Surjective (directSumIsotypicEval k A S M) := by
  rw [← LinearMap.range_eq_top, range_directSumIsotypicEval, eq_top_iff,
    ← IsSemisimpleModule.sSup_simples_eq_top]
  refine sSup_le fun m hm => ?_
  obtain ⟨j, ⟨e⟩⟩ := hcover m hm
  exact m.le_isotypicComponent.trans <| e.symm.isotypicComponent_eq.le.trans <|
    le_iSup (fun j => isotypicComponent A M (S j)) j

end DirectSum

section DirectSumEquiv

variable (k : Type*) {A : Type*} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  {κ : Type*} [DecidableEq κ] (S : κ → Type*) [∀ j, AddCommGroup (S j)] [∀ j, Module k (S j)]
  [∀ j, Module A (S j)] [∀ j, IsScalarTower k A (S j)] [∀ j, IsSimpleModule A (S j)]
  [∀ j, FiniteDimensional k (S j)]
  {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- For pairwise non-isomorphic simple modules `S j`, finite-dimensional over the algebraically
closed field `k`, evaluation `⨁ⱼ S j ⊗[k] (S j →ₗ[A] M) → M` is injective. No finiteness is asked
of `M`. -/
theorem directSumIsotypicEval_injective (hS : ∀ i j, Nonempty (S i ≃ₗ[A] S j) → i = j) :
    Function.Injective (directSumIsotypicEval k A S M) := by
  -- Each summand maps injectively onto its isotypic component, and these are independent.
  have hind : iSupIndep fun j => LinearMap.range (isotypicEval k (A := A) (S := S j) (M := M)) := by
    simpa only [range_isotypicEval] using iSupIndep_isotypicComponent A M S hS
  rw [directSumIsotypicEval_eq_lsum_comp, LinearMap.coe_comp]
  exact hind.dfinsupp_lsum_injective.comp <|
    (DFinsupp.mapRange_injective _ fun _ => map_zero _).mpr fun _ =>
      (LinearMap.injective_rangeRestrict_iff _).mpr (isotypicEval_injective k)

/-- **The isotypic decomposition of a semisimple module.** Let `S j` be pairwise non-isomorphic
simple modules, finite-dimensional over the algebraically closed field `k`, such that every simple
submodule of the semisimple module `M` is isomorphic to one of them. Then evaluation
`s ⊗ f ↦ f s` is an isomorphism `⨁ⱼ S j ⊗[k] (S j →ₗ[A] M) ≃ M` of `A`-modules. -/
noncomputable def directSumIsotypicTensorEquiv [IsSemisimpleModule A M]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[A] S j) → i = j)
    (hcover : ∀ m : Submodule A M, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m)) :
    (Π₀ j, S j ⊗[k] (S j →ₗ[A] M)) ≃ₗ[A] M :=
  .ofBijective (directSumIsotypicEval k A S M)
    ⟨directSumIsotypicEval_injective k S hS, directSumIsotypicEval_surjective k S hcover⟩

/-- `directSumIsotypicTensorEquiv` is the summed evaluation map. -/
@[simp]
theorem directSumIsotypicTensorEquiv_apply [IsSemisimpleModule A M]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[A] S j) → i = j)
    (hcover : ∀ m : Submodule A M, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m))
    (x : Π₀ j, S j ⊗[k] (S j →ₗ[A] M)) :
    directSumIsotypicTensorEquiv k S hS hcover x = directSumIsotypicEval k A S M x :=
  (rfl)

-- Not `@[simp]`: `directSumIsotypicTensorEquiv_apply` and `DFinsupp.mapRange.linearMap_apply`
-- already rewrite the left-hand side.
/-- **The isotypic decomposition is natural in the target.** An `A`-linear map `g : M →ₗ[A] N`
between semisimple modules acts on each multiplicity space `S j →ₗ[A] M` by postcomposition, and
on nothing else: this is `TauCeti.directSumIsotypicEval_comp` read through the equivalences. -/
theorem directSumIsotypicTensorEquiv_map [IsSemisimpleModule A M] [IsSemisimpleModule A N]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[A] S j) → i = j)
    (hcoverM : ∀ m : Submodule A M, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m))
    (hcoverN : ∀ m : Submodule A N, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m))
    (g : M →ₗ[A] N) (x : Π₀ j, S j ⊗[k] (S j →ₗ[A] M)) :
    directSumIsotypicTensorEquiv k S hS hcoverN
        (DFinsupp.mapRange.linearMap (fun j =>
          AlgebraTensorModule.map (LinearMap.id (R := A) (M := S j))
            (LinearMap.compRight (M := S j) k g)) x) =
      g (directSumIsotypicTensorEquiv k S hS hcoverM x) := by
  rw [directSumIsotypicTensorEquiv_apply, directSumIsotypicTensorEquiv_apply,
    directSumIsotypicEval_map_apply]

/-- **Transporting a map to the multiplicity spaces.** Reading
`TauCeti.directSumIsotypicTensorEquiv_map` backwards: the inverse equivalences carry an
`A`-linear map `g : M →ₗ[A] N` to `1 ⊗ (g ∘ ·)` on every summand. For `N = M` this says that
under the decomposition the commutant of `A` acts on the multiplicity spaces and trivially on the
`S j`. -/
@[simp]
theorem directSumIsotypicTensorEquiv_symm_apply_map [IsSemisimpleModule A M]
    [IsSemisimpleModule A N] (hS : ∀ i j, Nonempty (S i ≃ₗ[A] S j) → i = j)
    (hcoverM : ∀ m : Submodule A M, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m))
    (hcoverN : ∀ m : Submodule A N, IsSimpleModule A m → ∃ j, Nonempty (S j ≃ₗ[A] m))
    (g : M →ₗ[A] N) (y : M) :
    (directSumIsotypicTensorEquiv k S hS hcoverN).symm (g y) =
      DFinsupp.mapRange.linearMap (fun j =>
        AlgebraTensorModule.map (LinearMap.id (R := A) (M := S j))
          (LinearMap.compRight (M := S j) k g))
        ((directSumIsotypicTensorEquiv k S hS hcoverM).symm y) := by
  apply (directSumIsotypicTensorEquiv k S hS hcoverN).injective
  rw [LinearEquiv.apply_symm_apply, directSumIsotypicTensorEquiv_map k S hS hcoverM hcoverN,
    LinearEquiv.apply_symm_apply]

end DirectSumEquiv

end TauCeti
