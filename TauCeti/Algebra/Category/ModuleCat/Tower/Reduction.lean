/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.Algebra.Category.ModuleCat.Tower.AdicSystem

import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# Finite modules over a complete ring as adic systems

Let `I` be an ideal of a commutative ring `A`. The reductions `M ⧸ I M ← M ⧸ I² M ← ⋯` of an
`A`-module `M` form a tower, the *reduction* of `M`, which is an `I`-adic system. Its limit is the
`I`-adic completion of `M`, so `M` is recovered from its reduction exactly when it is `I`-adically
complete.

Conversely, the limit `L` of an `I`-adic system `(Mₙ)` with `M₀` finite over an `I`-adically
precomplete ring is a finite module whose reduction is `(Mₙ)` again
(`ModuleTower.IsAdicSystem.reductionLimIso`), and linear maps into an `I`-adically complete module
are exactly the morphisms of the reductions (`ModuleTower.reductionMap_bijective`). Hence over a
noetherian `I`-adically complete ring, reduction is an equivalence from finite modules to `I`-adic
systems with finite `M₀` (EGA I, Ch. 0, 7.2.9–7.2.10). Over an adic noetherian ring with ideal of
definition `I`, these are the compatible systems of finite modules over the truncations
`A ⧸ I^{n+1}`; this is the affine case of the description of coherent modules on a noetherian
formal scheme as compatible systems of coherent modules on its thickenings.

## Main definitions

* `TauCeti.ModuleTower.reduction`: the tower `n ↦ M ⧸ I^{n+1} M` of an `A`-module `M`.
* `TauCeti.ModuleTower.reductionπ`, `TauCeti.ModuleTower.reductionLift`: the quotient maps onto the
  terms of the reduction and their universal property.
* `TauCeti.ModuleTower.reductionMap`, `TauCeti.ModuleTower.reductionFunctor`: reduction of linear
  maps, and reduction as a functor from `A`-modules to towers.
* `TauCeti.ModuleTower.limReductionEquiv`: the limit of the reduction is the adic completion.
* `TauCeti.ModuleTower.toLimReduction`: the canonical map from `M` to the limit of its reduction.
* `TauCeti.ModuleTower.FiniteAdicSystem`: the category of `I`-adic systems with finite `M₀`.
* `TauCeti.ModuleTower.finiteReduction`: reduction of finite modules to finite adic systems.

## Main results

* `TauCeti.ModuleTower.isAdicSystem_reduction`: the reduction of a module is an `I`-adic system.
* `TauCeti.ModuleTower.toLimReduction_bijective`: an `I`-adically complete module is the limit of
  its reduction.
* `TauCeti.ModuleTower.reductionMap_bijective`: linear maps into an `I`-adically complete
  module are the morphisms of the reductions.
* `TauCeti.ModuleTower.IsAdicSystem.reductionLimIso`: an `I`-adic system with finite `M₀` over an
  `I`-adically precomplete ring is the reduction of its limit.
* `TauCeti.ModuleTower.finiteReduction_isEquivalence`: over a noetherian `I`-adically complete
  ring, reduction is an equivalence from finite modules to `I`-adic systems with finite `M₀`.
* `TauCeti.ModuleTower.toLimReduction_injective_iff`, `toLimReduction_surjective_iff`: `M` maps
  injectively (surjectively) to the limit of its reduction iff it is `I`-adically Hausdorff
  (precomplete).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.2.9–7.2.10.
* [Stacks: Lemma 30.23.1, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

public section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### The reduction of a module -/

section Reduction

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- The *reduction* of an `A`-module `M` along an ideal `I`: the tower
`M ⧸ I M ← M ⧸ I² M ← M ⧸ I³ M ← ⋯` with the quotient maps as transitions. Its terms are
handled through the quotient maps `ModuleTower.reductionπ` and their universal property
`ModuleTower.reductionLift`. -/
noncomputable def reduction : ModuleTower.{v} A where
  obj n := ModuleCat.of A (M ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule A M))
  map f := ModuleCat.ofHom (Submodule.factorPow I M (Nat.add_le_add_right (leOfHom f.unop) 1))
  -- The composites of quotient maps are quotient maps, by definition of `Submodule.factorPow`.
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The quotient map from `M` onto the `n`-th term `M ⧸ I^{n+1} M` of its reduction. -/
noncomputable def reductionπ (n : ℕ) : M →ₗ[A] (reduction I M).obj (op n) :=
  (I ^ (n + 1) • ⊤ : Submodule A M).mkQ

theorem reductionπ_surjective (n : ℕ) : Function.Surjective (reductionπ I M n) :=
  Submodule.mkQ_surjective _

@[simp]
theorem ker_reductionπ (n : ℕ) : LinearMap.ker (reductionπ I M n) = I ^ (n + 1) • ⊤ :=
  Submodule.ker_mkQ _

/-- Linear maps out of a term of the reduction agree once they agree on `M`. -/
@[ext]
theorem reduction_hom_ext {P : Type*} [AddCommGroup P] [Module A P] {n : ℕ}
    {f g : (reduction I M).obj (op n) →ₗ[A] P}
    (h : f ∘ₗ reductionπ I M n = g ∘ₗ reductionπ I M n) : f = g :=
  Submodule.linearMap_qext _ h

/-- The universal property of the `n`-th term of the reduction: a linear map `M → P` killing
`I^{n+1} M` factors through `M ⧸ I^{n+1} M`. -/
noncomputable def reductionLift {P : Type*} [AddCommGroup P] [Module A P] (n : ℕ)
    (f : M →ₗ[A] P) (hf : I ^ (n + 1) • (⊤ : Submodule A M) ≤ LinearMap.ker f) :
    (reduction I M).obj (op n) →ₗ[A] P :=
  (I ^ (n + 1) • ⊤ : Submodule A M).liftQ f hf

@[simp]
theorem reductionLift_reductionπ {P : Type*} [AddCommGroup P] [Module A P] (n : ℕ)
    (f : M →ₗ[A] P) (hf : I ^ (n + 1) • (⊤ : Submodule A M) ≤ LinearMap.ker f) (x : M) :
    reductionLift I M n f hf (reductionπ I M n x) = f x :=
  Submodule.liftQ_apply _ f x

@[simp]
theorem transitionOfLE_reductionπ {n k : ℕ} (h : n ≤ k) (x : M) :
    (reduction I M).transitionOfLE h (reductionπ I M k x) = reductionπ I M n x := by
  -- The transitions of `reduction` are the quotient maps `Submodule.factorPow`, by definition.
  rw [transitionOfLE_def]
  rfl

@[simp]
theorem transitionOfLE_comp_reductionπ {n k : ℕ} (h : n ≤ k) :
    (reduction I M).transitionOfLE h ∘ₗ reductionπ I M k = reductionπ I M n :=
  LinearMap.ext (transitionOfLE_reductionπ I M h)

@[simp]
theorem transition_comp_reductionπ (n : ℕ) :
    (reduction I M).transition n ∘ₗ reductionπ I M (n + 1) = reductionπ I M n := by
  rw [← transitionOfLE_succ, transitionOfLE_comp_reductionπ]

@[simp]
theorem transition_reductionπ (n : ℕ) (x : M) :
    (reduction I M).transition n (reductionπ I M (n + 1) x) = reductionπ I M n x :=
  LinearMap.congr_fun (transition_comp_reductionπ I M n) x

/-- **The reduction of a module is an `I`-adic system.** -/
theorem isAdicSystem_reduction : (reduction I M).IsAdicSystem I where
  transition_surjective n := by
    refine Function.Surjective.of_comp (g := reductionπ I M (n + 1)) ?_
    rw [← LinearMap.coe_comp, transition_comp_reductionπ]
    exact reductionπ_surjective I M n
  ker_transition n := by
    rw [← Submodule.map_comap_eq_of_surjective (reductionπ_surjective I M (n + 1))
      (LinearMap.ker _), ← LinearMap.ker_comp, transition_comp_reductionπ, ker_reductionπ,
      Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.2 (reductionπ_surjective I M (n + 1))]

/-- The canonical map `M → lim (M ⧸ I^{n+1} M)` from a module to the limit of its reduction. -/
noncomputable def toLimReduction : M →ₗ[A] (reduction I M).lim :=
  (reduction I M).limLift (reductionπ I M) (transition_comp_reductionπ I M)

@[simp]
theorem limπ_comp_toLimReduction (n : ℕ) :
    (reduction I M).limπ n ∘ₗ toLimReduction I M = reductionπ I M n := by
  rw [toLimReduction, limπ_comp_limLift]

@[simp]
theorem coe_toLimReduction_apply (x : M) (n : ℕ) :
    (toLimReduction I M x : (reduction I M).Product) n = reductionπ I M n x := by
  rw [← limπ_apply, ← LinearMap.comp_apply, limπ_comp_toLimReduction]

/-- Two elements of `M` have the same image in `M ⧸ I^{n+1} M` exactly when they are congruent
modulo `I^{n+1} M`. -/
theorem reductionπ_eq_reductionπ_iff {n : ℕ} {x y : M} :
    reductionπ I M n x = reductionπ I M n y ↔ x ≡ y [SMOD (I ^ (n + 1) • ⊤ : Submodule A M)] := by
  rw [SModEq.sub_mem, ← ker_reductionπ I M n, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- The map `M ⧸ I^{n+1} M → M ⧸ I^n M` from the `n`-th term of the reduction to the `n`-th term
of Mathlib's adic completion. -/
private noncomputable def toAdicQuotient (n : ℕ) :
    (reduction I M).obj (op n) →ₗ[A] M ⧸ (I ^ n • ⊤ : Submodule A M) :=
  reductionLift I M n (I ^ n • ⊤ : Submodule A M).mkQ <| by
    rw [Submodule.ker_mkQ]
    exact Submodule.pow_smul_top_le I M n.le_succ

private theorem toAdicQuotient_reductionπ (n : ℕ) (x : M) :
    toAdicQuotient I M n (reductionπ I M n x) = Submodule.Quotient.mk x :=
  reductionLift_reductionπ I M n _ _ x

/-- The map `M ⧸ I^{n+1} M → M ⧸ I^{n+1} M` from the `(n + 1)`-st term of Mathlib's adic completion
to the `n`-th term of the reduction. -/
private noncomputable def ofAdicQuotient (n : ℕ) :
    M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M) →ₗ[A] (reduction I M).obj (op n) :=
  (I ^ (n + 1) • ⊤ : Submodule A M).liftQ (reductionπ I M n) (ker_reductionπ I M n).ge

private theorem ofAdicQuotient_mk (n : ℕ) (x : M) :
    ofAdicQuotient I M n (Submodule.Quotient.mk x) = reductionπ I M n x :=
  Submodule.liftQ_apply _ _ x

/-- The map `lim (M ⧸ I^{n+1} M) → AdicCompletion I M`, reindexing compatible families. -/
private noncomputable def toAdicCompletion : (reduction I M).lim →ₗ[A] AdicCompletion I M :=
  AdicCompletion.lift I (fun n ↦ toAdicQuotient I M n ∘ₗ (reduction I M).limπ n)
    fun {m n} hmn ↦ by
      ext y
      obtain ⟨x, hx⟩ := reductionπ_surjective I M n ((reduction I M).limπ n y)
      simp only [LinearMap.comp_apply, ← (reduction I M).transitionOfLE_comp_limπ hmn, ← hx,
        transitionOfLE_reductionπ, toAdicQuotient_reductionπ, Submodule.mapQ_apply,
        LinearMap.id_apply]

/- This is `AdicCompletion.eval_lift_apply`, which holds by definition; stating it through `rfl`
avoids restating the compatibility proof of `toAdicCompletion` to unify with its argument. -/
private theorem toAdicCompletion_val (y : (reduction I M).lim) (n : ℕ) :
    (toAdicCompletion I M y).val n = toAdicQuotient I M n ((reduction I M).limπ n y) :=
  rfl

/-- The map `AdicCompletion I M → lim (M ⧸ I^{n+1} M)`, reindexing compatible families. -/
private noncomputable def ofAdicCompletion : AdicCompletion I M →ₗ[A] (reduction I M).lim :=
  (reduction I M).limLift (fun n ↦ ofAdicQuotient I M n ∘ₗ AdicCompletion.eval I M (n + 1))
    fun n ↦ by
      -- Elements of the completion are represented by adic Cauchy sequences.
      ext x
      simp only [LinearMap.comp_apply, AdicCompletion.eval_apply, AdicCompletion.mk_apply_coe,
        Submodule.mkQ_apply, ofAdicQuotient_mk, transition_reductionπ]
      exact (reductionπ_eq_reductionπ_iff I M).2 (x.2 (n + 1).le_succ).symm

private theorem limπ_ofAdicCompletion (x : AdicCompletion I M) (n : ℕ) :
    (reduction I M).limπ n (ofAdicCompletion I M x) = ofAdicQuotient I M n (x.val (n + 1)) := by
  rw [ofAdicCompletion, ← LinearMap.comp_apply, limπ_comp_limLift, LinearMap.comp_apply,
    AdicCompletion.eval_apply]

/-- **The limit of the reduction of `M` is the `I`-adic completion of `M`.** The two differ only in
their indexing: Mathlib's `AdicCompletion I M` uses the quotients `M ⧸ I^n M` from `n = 0`. -/
noncomputable def limReductionEquiv : (reduction I M).lim ≃ₗ[A] AdicCompletion I M :=
  LinearEquiv.ofLinearMap (toAdicCompletion I M) (ofAdicCompletion I M)
    (by
      ext x n
      simp only [LinearMap.comp_apply, toAdicCompletion_val, limπ_ofAdicCompletion,
        AdicCompletion.mk_apply_coe, Submodule.mkQ_apply, ofAdicQuotient_mk,
        toAdicQuotient_reductionπ, LinearMap.id_apply]
      exact (x.2 n.le_succ).symm)
    (by
      ext n y
      obtain ⟨x, hx⟩ := reductionπ_surjective I M (n + 1) ((reduction I M).limπ (n + 1) y)
      have hy : (reduction I M).limπ n y = reductionπ I M n x := by
        rw [← (reduction I M).transition_comp_limπ n, LinearMap.comp_apply, ← hx,
          transition_reductionπ]
      simp only [LinearMap.comp_apply, limπ_ofAdicCompletion, toAdicCompletion_val, ← hx, hy,
        toAdicQuotient_reductionπ, ofAdicQuotient_mk, LinearMap.id_apply])

@[simp]
theorem limReductionEquiv_toLimReduction (x : M) :
    limReductionEquiv I M (toLimReduction I M x) = AdicCompletion.of I M x := by
  ext n
  simp only [limReductionEquiv, LinearEquiv.coe_ofLinearMap, toAdicCompletion_val, limπ_apply,
    coe_toLimReduction_apply, toAdicQuotient_reductionπ, AdicCompletion.of_apply,
    Submodule.mkQ_apply]

theorem toLimReduction_eq :
    toLimReduction I M = (limReductionEquiv I M).symm.toLinearMap ∘ₗ AdicCompletion.of I M :=
  LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply,
      limReductionEquiv_toLimReduction]

/-- The canonical map to the limit of the reduction is injective exactly when `M` is
`I`-adically Hausdorff. -/
theorem toLimReduction_injective_iff :
    Function.Injective (toLimReduction I M) ↔ IsHausdorff I M := by
  rw [toLimReduction_eq, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact ((limReductionEquiv I M).symm.toEquiv.comp_injective _).trans
    AdicCompletion.of_injective_iff

/-- The canonical map to the limit of the reduction is surjective exactly when `M` is
`I`-adically precomplete. -/
theorem toLimReduction_surjective_iff :
    Function.Surjective (toLimReduction I M) ↔ IsPrecomplete I M := by
  rw [toLimReduction_eq, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact ((limReductionEquiv I M).symm.toEquiv.comp_surjective _).trans
    AdicCompletion.of_surjective_iff

/-- **An `I`-adically complete module is the limit of its reduction.** -/
theorem toLimReduction_bijective [IsAdicComplete I M] : Function.Bijective (toLimReduction I M) :=
  ⟨(toLimReduction_injective_iff I M).2 inferInstance,
    (toLimReduction_surjective_iff I M).2 inferInstance⟩

end Reduction

/-! ### Reduction as a functor -/

section Functor

variable {M N P : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  [AddCommGroup P] [Module A P]

/-- Composing a linear map `M → N` with the quotient map of `N` kills `I^{n+1} M`. -/
private theorem pow_smul_top_le_ker_reductionπ_comp (u : M →ₗ[A] N) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A M) ≤ LinearMap.ker (reductionπ I N n ∘ₗ u) := by
  rw [LinearMap.ker_comp, ker_reductionπ]
  exact Submodule.smul_top_le_comap_smul_top _ _

/-- The `n`-th component `M ⧸ I^{n+1} M → N ⧸ I^{n+1} N` of `ModuleTower.reductionMap`. -/
private noncomputable def reductionMapApp (u : M →ₗ[A] N) (n : ℕ) :
    (reduction I M).obj (op n) →ₗ[A] (reduction I N).obj (op n) :=
  reductionLift I M n (reductionπ I N n ∘ₗ u) (pow_smul_top_le_ker_reductionπ_comp I u n)

private theorem reductionMapApp_reductionπ (u : M →ₗ[A] N) (n : ℕ) (x : M) :
    reductionMapApp I u n (reductionπ I M n x) = reductionπ I N n (u x) :=
  reductionLift_reductionπ I M n _ _ x

/-- The morphism `M ⧸ I^{n+1} M ⟶ N ⧸ I^{n+1} N` of `A`-modules given by `reductionMapApp`. The
module structures are those of the terms of the reductions, so that `ModuleCat.ofHom` does not
unfold `reduction`. -/
private noncomputable def reductionMapHom (u : M →ₗ[A] N) (n : ℕ) :
    (reduction I M).obj (op n) ⟶ (reduction I N).obj (op n) :=
  @ModuleCat.ofHom A _ _ _ _ ((reduction I M).obj (op n)).isModule _
    ((reduction I N).obj (op n)).isModule (reductionMapApp I u n)

private theorem hom_reductionMapHom (u : M →ₗ[A] N) (n : ℕ) :
    (reductionMapHom I u n).hom = reductionMapApp I u n :=
  ModuleCat.hom_ofHom _

/-- The morphism of reductions given by the maps `M ⧸ I^{n+1} M → N ⧸ I^{n+1} N` induced by a
linear map `u : M → N`. -/
noncomputable def reductionMap (u : M →ₗ[A] N) : reduction I M ⟶ reduction I N :=
  NatTrans.ofOpSequence (reductionMapHom I u) fun n ↦ by
    ext x
    simp [hom_reductionMapHom, reductionMapApp_reductionπ]

@[simp]
theorem reductionMap_app_reductionπ (u : M →ₗ[A] N) (n : ℕ) (x : M) :
    ((reductionMap I u).app (op n)).hom (reductionπ I M n x) = reductionπ I N n (u x) := by
  rw [reductionMap, NatTrans.ofOpSequence_app, hom_reductionMapHom, reductionMapApp_reductionπ]

@[simp]
theorem reductionMap_id : reductionMap I (LinearMap.id : M →ₗ[A] M) = 𝟙 (reduction I M) := by
  ext ⟨n⟩ x
  simp

theorem reductionMap_comp (u : M →ₗ[A] N) (w : N →ₗ[A] P) :
    reductionMap I (w ∘ₗ u) = reductionMap I u ≫ reductionMap I w := by
  ext ⟨n⟩ x
  simp

/-- The canonical maps to the limits of the reductions are natural. -/
@[simp]
theorem limMap_reductionMap_toLimReduction (u : M →ₗ[A] N) (x : M) :
    limMap (reductionMap I u) (toLimReduction I M x) = toLimReduction I N (u x) :=
  Subtype.ext <| funext fun n ↦ by simp

/-- Reduction along `I` as a functor from `A`-modules to towers. -/
@[expose]
noncomputable def reductionFunctor : ModuleCat.{v} A ⥤ ModuleTower.{v} A where
  obj M := reduction I M
  map u := reductionMap I u.hom
  map_id _ := reductionMap_id I
  map_comp _ _ := reductionMap_comp I _ _

@[simp]
theorem reductionFunctor_obj (M : ModuleCat.{v} A) : (reductionFunctor I).obj M = reduction I M :=
  (rfl)

@[simp]
theorem reductionFunctor_map {M N : ModuleCat.{v} A} (u : M ⟶ N) :
    (reductionFunctor I).map u = reductionMap I u.hom :=
  (rfl)

variable {I}

/-- **Linear maps into an `I`-adically complete module are the morphisms of the reductions**
(EGA I, Ch. 0, 7.2.10): `u ↦ (u mod I^{n+1})ₙ` is a bijection. The source module is arbitrary. -/
theorem reductionMap_bijective [IsAdicComplete I N] :
    Function.Bijective (reductionMap I : (M →ₗ[A] N) → (reduction I M ⟶ reduction I N)) := by
  let e := LinearEquiv.ofBijective _ (toLimReduction_bijective I N)
  refine ⟨fun u v huv ↦ LinearMap.ext fun x ↦ e.injective ?_, fun f ↦ ?_⟩
  · simp only [e, LinearEquiv.ofBijective_apply, ← limMap_reductionMap_toLimReduction, huv]
  -- The preimage of `f` is `M → lim (M ⧸ I^{n+1} M) → lim (N ⧸ I^{n+1} N) ≃ N`.
  refine ⟨e.symm.toLinearMap ∘ₗ limMap f ∘ₗ toLimReduction I M, ?_⟩
  ext ⟨n⟩ x
  have hx : toLimReduction I N (e.symm (limMap f (toLimReduction I M x))) =
      limMap f (toLimReduction I M x) :=
    e.apply_symm_apply _
  simpa using congr((reduction I N).limπ n $hx)

end Functor

/-! ### Adic systems as reductions of their limits -/

namespace IsAdicSystem

variable {I} {F : ModuleTower.{v} A} (hF : F.IsAdicSystem I) [IsPrecomplete I A]
  [Module.Finite A (F.obj (op 0))]

/-- The isomorphism `lim Mₙ ⧸ I^{n+1} lim Mₙ ≃ Mₙ` of `ModuleTower.IsAdicSystem.limQuotientEquiv`,
with source the `n`-th term of the reduction of `lim Mₙ`, which is that quotient by definition. -/
noncomputable def reductionLimEquiv (n : ℕ) : (reduction I F.lim).obj (op n) ≃ₗ[A] F.obj (op n) :=
  hF.limQuotientEquiv n

@[simp]
theorem reductionLimEquiv_reductionπ (n : ℕ) (x : F.lim) :
    hF.reductionLimEquiv n (reductionπ I F.lim n x) = F.limπ n x :=
  -- `reductionπ` is the quotient map `Submodule.mkQ`, by definition.
  hF.limQuotientEquiv_mk n x

/-- **An `I`-adic system is the reduction of its limit** (EGA I, Ch. 0, 7.2.9), over an
`I`-adically precomplete ring with `M₀` finite: the isomorphisms `lim Mₙ ⧸ I^{n+1} ≃ Mₙ` are
compatible with the transitions. -/
noncomputable def reductionLimIso : reduction I F.lim ≅ F :=
  NatIso.ofComponents (fun n ↦ (hF.reductionLimEquiv n.unop).toModuleIso) <| by
    rintro ⟨n⟩ ⟨k⟩ f
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom]
    simp

@[simp]
theorem reductionLimIso_hom_app_reductionπ (n : ℕ) (x : F.lim) :
    (hF.reductionLimIso.hom.app (op n)).hom (reductionπ I F.lim n x) = F.limπ n x := by
  simp only [reductionLimIso, NatIso.ofComponents_hom_app, LinearEquiv.toModuleIso_hom]
  rw [ModuleCat.hom_ofHom]
  exact hF.reductionLimEquiv_reductionπ n x

end IsAdicSystem

/-! ### The equivalence between finite modules and finite adic systems -/

section Finite

/-- The property of a tower of being an `I`-adic system with finite term `M₀`. -/
@[expose]
def isFiniteAdicSystem : ObjectProperty (ModuleTower.{v} A) :=
  fun F ↦ F.IsAdicSystem I ∧ Module.Finite A (F.obj (op 0))

/-- The category of `I`-adic systems with finite term `M₀`, a full subcategory of the towers of
`A`-modules. -/
abbrev FiniteAdicSystem := (isFiniteAdicSystem.{v} I).FullSubcategory

/-- Reduction of finite `A`-modules to `I`-adic systems with finite `M₀`. -/
@[expose]
noncomputable def finiteReduction : FGModuleCat.{v} A ⥤ FiniteAdicSystem.{v} I :=
  (isFiniteAdicSystem I).lift ((ModuleCat.isFG A).ι ⋙ reductionFunctor I) fun M ↦
    ⟨isAdicSystem_reduction I M, .of_surjective _ (reductionπ_surjective I M 0)⟩

@[simp]
theorem finiteReduction_obj_obj (M : FGModuleCat.{v} A) :
    ((finiteReduction I).obj M).obj = reduction I M :=
  (rfl)

@[simp]
theorem finiteReduction_map_hom {M N : FGModuleCat.{v} A} (u : M ⟶ N) :
    ((finiteReduction I).map u).hom = (reductionFunctor I).map u.hom :=
  (rfl)

instance [IsNoetherianRing A] [IsAdicComplete I A] : (finiteReduction I).Faithful where
  map_injective {M N} u v huv := by
    have := IsAdicComplete.of_finite I N
    exact FGModuleCat.hom_ext <| reductionMap_bijective.1 congr(($huv).hom)

instance [IsNoetherianRing A] [IsAdicComplete I A] : (finiteReduction I).Full where
  map_surjective {M N} f := by
    have := IsAdicComplete.of_finite I N
    obtain ⟨u, hu⟩ := (reductionMap_bijective (M := M) (N := N)).2 f.hom
    exact ⟨ObjectProperty.homMk (ModuleCat.ofHom u), ObjectProperty.hom_ext _ hu⟩

/-- Every `I`-adic system with finite `M₀` over an `I`-adically precomplete ring is the reduction
of a finite module, its limit. -/
instance [IsPrecomplete I A] : (finiteReduction.{v} I).EssSurj where
  mem_essImage F := by
    obtain ⟨hF, _⟩ := F.property
    have := hF.finite_lim
    exact ⟨FGModuleCat.of A F.obj.lim, ⟨ObjectProperty.isoMk _ hF.reductionLimIso⟩⟩

/-- **Finite modules are finite adic systems** (EGA I, Ch. 0, 7.2.9–7.2.10): over a noetherian
`I`-adically complete ring, `M ↦ (M ⧸ I^{n+1} M)ₙ` is an equivalence from finite `A`-modules to
`I`-adic systems with finite `M₀`, with quasi-inverse the limit. -/
instance finiteReduction_isEquivalence [IsNoetherianRing A] [IsAdicComplete I A] :
    (finiteReduction.{v} I).IsEquivalence where

end Finite

end TauCeti.ModuleTower
