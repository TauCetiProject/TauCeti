/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PiTensorProduct.Map
public import TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Evens' twisted multiplication on tensor-induced `G`-algebras

When `A` is a commutative `G`-algebra over `R` and `G ⧸ U` is finite, Evens' twisted
multiplication
```text
⨂[R] _ : G ⧸ U, A ⟶ A,     ⨂ₜ x, a x ↦ ∏ x : G ⧸ U, r_s(x) • a x
```
is a `G`-equivariant `R`-algebra homomorphism (`Subgroup.tensorInducedMulAlgHom`, bundled on
`Subgroup.TensorInduced` as `Subgroup.TensorInduced.mulSemiringActionHom`), independent of the
chosen left transversal up to `Subgroup.tensorInducedChangeTransversalAlgEquiv`, and transitive
along subgroup towers `V ≤ U ≤ G`.

## Main definitions

* `Subgroup.tensorInducedMulAlgHom`, `Subgroup.tensorInducedMulIntertwiningMap`: Evens' twisted
  multiplication `⨂ₜ x, a x ↦ ∏ x, r_s(x) • a x` as an `R`-algebra homomorphism and as a
  `G`-intertwining `R`-linear map.
* `Subgroup.TensorInduced.mulAlgHom`, `Subgroup.TensorInduced.mulSemiringActionHom`: Evens' twisted
  multiplication on the bundled carrier `U.TensorInduced s R A`, as an `R`-algebra homomorphism and
  as a homomorphism of `G`-semirings `U.TensorInduced s R A →+*[G] A`.

## Main results

* `Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut`,
  `Subgroup.TensorInduced.mulAlgHom_smul`: `G`-equivariance of Evens' twisted multiplication.
* `Subgroup.tensorInducedMulAlgHom_changeTransversal`,
  `Subgroup.tensorInducedMulAlgHom_comp_changeTransversal`,
  `Subgroup.TensorInduced.mulSemiringActionHom_comp_changeTransversal`: independence of the chosen
  left transversal.
* `Subgroup.tensorInducedMulAlgHom_transitivity`: compatibility of Evens' twisted multiplication
  with transitivity along `V ≤ U ≤ G`.
* `Subgroup.tensorInducedMulAlgHom_of_smul_eq_self`,
  `Subgroup.tensorInducedMulAlgHom_tprod_const_of_smul_eq`: specialization to trivial `G`-actions
  and `G`-fixed elements.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society **108** (1963), §§5–6, pp. 60–62.
-/

public section

open scoped TensorProduct

universe u v w

namespace Subgroup

open TauCeti

section Multiplication

variable {G : Type v} [Group G] (U : Subgroup G) (s : U.LeftTransversal) [Fintype (G ⧸ U)]
  (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- **Evens' twisted multiplication** on the tensor-induced commutative `R`-algebra:
it sends a pure tensor `⨂ₜ x, m x` to `∏ x : G ⧸ U, r_s(x) • m x`, where
`r_s = U.leftTransversalRep s`. -/
noncomputable def tensorInducedMulAlgHom : (⨂[R] _ : G ⧸ U, A) →ₐ[R] A :=
  PiTensorProduct.mulAlgHom.comp
    (PiTensorProduct.mapAlgHom fun x : G ⧸ U ↦
      MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x))

/-- On a pure tensor, `tensorInducedMulAlgHom` acts on each coset slot by its chosen transversal
representative and multiplies the results in `A`. -/
@[simp]
theorem tensorInducedMulAlgHom_tprod (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x := by
  simp [tensorInducedMulAlgHom]

/-- On a factor inclusion at coset `x`, `tensorInducedMulAlgHom` acts by the chosen coset
representative `U.leftTransversalRep s x`. It is a pre-simp lemma since `singleAlgHom_apply` would
otherwise unfold the factor inclusion first. -/
@[simp↓]
theorem tensorInducedMulAlgHom_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.singleAlgHom x a) =
      U.leftTransversalRep s x • a := by
  rw [tensorInducedMulAlgHom, AlgHom.comp_apply, PiTensorProduct.mapAlgHom_singleAlgHom,
    PiTensorProduct.mulAlgHom_singleAlgHom]
  rfl

/-- **Equivariance of Evens' twisted multiplication.** For every `g : G`,
`U.tensorInducedMulAlgHom s R A` intertwines `U.tensorInducedAlgAut s R A g` with the `G`-action
on `A`. -/
theorem tensorInducedMulAlgHom_tensorInducedAlgAut (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A (U.tensorInducedAlgAut s R A g z) =
      g • U.tensorInducedMulAlgHom s R A z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, tensorInducedAlgAut_apply_tprod, tensorInducedMulAlgHom_tprod,
      smul_comm g r]
    congr 1
    have hslot (x : G ⧸ U) :
        U.leftTransversalRep s x • ((U.monomialHom s g).left x • m (g⁻¹ • x)) =
          g • (U.leftTransversalRep s (g⁻¹ • x) • m (g⁻¹ • x)) := by
      rw [monomialHom_left, Subgroup.mk_smul, ← mul_smul, transversal_mul_lWord, mul_smul]
    have hprod :
        ∏ x : G ⧸ U, g • (U.leftTransversalRep s (g⁻¹ • x) • m (g⁻¹ • x)) =
          g • ∏ x : G ⧸ U, U.leftTransversalRep s (g⁻¹ • x) • m (g⁻¹ • x) :=
      (map_prod (MulSemiringAction.toRingHom G A g)
        (fun x : G ⧸ U ↦ U.leftTransversalRep s (g⁻¹ • x) • m (g⁻¹ • x)) Finset.univ).symm
    simp_rw [hslot]
    exact hprod.trans <| congrArg (g • ·)
      (Equiv.prod_comp (MulAction.toPerm g⁻¹) fun x ↦ U.leftTransversalRep s x • m x)
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

/-- `U.tensorInducedMulAlgHom` intertwines `U.tensorInducedRepresentation` with the `G`-action on
`A`. -/
theorem tensorInducedMulAlgHom_tensorInducedRepresentation (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A
        (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z) =
      g • U.tensorInducedMulAlgHom s R A z := by
  rw [← tensorInducedAlgAut_apply_eq_tensorInducedRepresentation]
  exact U.tensorInducedMulAlgHom_tensorInducedAlgAut s R A g z

/-- Evens' twisted multiplication as a `G`-intertwining `R`-linear map from the tensor-induced
representation to `A`. -/
noncomputable def tensorInducedMulIntertwiningMap :
    (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)).IntertwiningMap
      (Representation.ofDistribMulAction R G A) where
  toLinearMap := (U.tensorInducedMulAlgHom s R A).toLinearMap
  isIntertwining' g := LinearMap.ext <|
    U.tensorInducedMulAlgHom_tensorInducedRepresentation s R A g

/-- The underlying `R`-linear map of `tensorInducedMulIntertwiningMap` is
`tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_toLinearMap :
    (U.tensorInducedMulIntertwiningMap s R A).toLinearMap =
      (U.tensorInducedMulAlgHom s R A).toLinearMap := (rfl)

/-- Evaluating `tensorInducedMulIntertwiningMap` gives `tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulIntertwiningMap s R A z = U.tensorInducedMulAlgHom s R A z := (rfl)

/-- **Independence of the transversal.** Applying `U.tensorInducedChangeTransversalAlgEquiv s t R A`
followed by `U.tensorInducedMulAlgHom s R A` gives `U.tensorInducedMulAlgHom t R A`. -/
@[simp]
theorem tensorInducedMulAlgHom_changeTransversal (t : U.LeftTransversal)
    (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A (U.tensorInducedChangeTransversalAlgEquiv s t R A z) =
      U.tensorInducedMulAlgHom t R A z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, tensorInducedChangeTransversalAlgEquiv_tprod, tensorInducedMulAlgHom_tprod]
    congr 1
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [monomialChangeTransversal_left, Subgroup.mk_smul, ← mul_smul,
      transversal_mul_transversalDiff]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Composition form of transversal independence for `U.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulAlgHom_comp_changeTransversal (t : U.LeftTransversal) :
    (U.tensorInducedMulAlgHom s R A).comp
        (U.tensorInducedChangeTransversalAlgEquiv s t R A).toAlgHom =
      U.tensorInducedMulAlgHom t R A :=
  AlgHom.ext <| U.tensorInducedMulAlgHom_changeTransversal s R A t

/-- When `G` acts trivially on `A`, `U.tensorInducedMulAlgHom` reduces to untwisted factorwise
multiplication `PiTensorProduct.mulAlgHom`. -/
theorem tensorInducedMulAlgHom_of_smul_eq_self (hA : ∀ (g : G) (a : A), g • a = a) :
    U.tensorInducedMulAlgHom s R A = PiTensorProduct.mulAlgHom := by
  refine AlgHom.toLinearMap_injective <| PiTensorProduct.ext <| MultilinearMap.ext fun m ↦ ?_
  simp [hA]

/-- On a constant pure tensor `⨂ₜ _, a`, `tensorInducedMulAlgHom` computes the multiplicative
orbit norm `∏ x : G ⧸ U, r_s(x) • a`. -/
theorem tensorInducedMulAlgHom_tprod_const (a : A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ a) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • a :=
  U.tensorInducedMulAlgHom_tprod s R A _

/-- On a `G`-fixed element `a : A`, `tensorInducedMulAlgHom` sends the constant pure tensor
`⨂ₜ _, a` to `a ^ U.index`. -/
theorem tensorInducedMulAlgHom_tprod_const_of_smul_eq {a : A} (ha : ∀ g : G, g • a = a) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ a) =
      a ^ U.index := by
  rw [tensorInducedMulAlgHom_tprod_const]
  simp [ha, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

/-- When `G ⧸ U` has a single coset and `1 ∈ s`, `tensorInducedMulAlgHom` evaluates a pure tensor
at the unique coset without twist. -/
theorem tensorInducedMulAlgHom_tprod_of_unique [Unique (G ⧸ U)] (h1 : (1 : G) ∈ (s : Set G))
    (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) = m default := by
  have hrep (q : G ⧸ U) : U.leftTransversalRep s q = 1 := by
    rw [Subsingleton.elim q ((1 : G) : G ⧸ U)]
    exact U.leftTransversalRep_mk_of_mem s h1
  rw [tensorInducedMulAlgHom_tprod, Fintype.prod_unique, hrep, one_smul]
  exact congrArg m (Subsingleton.elim _ _)

namespace TensorInduced

/-- Evens' twisted multiplication as an `R`-algebra homomorphism `U.TensorInduced s R A →ₐ[R] A`. -/
noncomputable def mulAlgHom : U.TensorInduced s R A →ₐ[R] A :=
  (U.tensorInducedMulAlgHom s R A).comp (algEquivTensor U s R A).toAlgHom

/-- `TensorInduced.mulAlgHom` evaluates `Subgroup.tensorInducedMulAlgHom` on `toTensor`. -/
theorem mulAlgHom_apply (z : U.TensorInduced s R A) :
    mulAlgHom U s R A z = U.tensorInducedMulAlgHom s R A z.toTensor := by
  simp [mulAlgHom]

/-- On `ofTensor z`, `TensorInduced.mulAlgHom` evaluates `Subgroup.tensorInducedMulAlgHom` on
`z`. -/
@[simp]
theorem mulAlgHom_ofTensor (z : ⨂[R] _ : G ⧸ U, A) :
    mulAlgHom U s R A (ofTensor z) = U.tensorInducedMulAlgHom s R A z := by
  simp [mulAlgHom]

/-- On a pure tensor, `TensorInduced.mulAlgHom` twists each coset entry by its transversal
representative and multiplies the results in `A`. -/
@[simp]
theorem mulAlgHom_tprod (m : G ⧸ U → A) :
    mulAlgHom U s R A (tprod m) = ∏ x : G ⧸ U, U.leftTransversalRep s x • m x := by
  rw [mulAlgHom_apply, toTensor_tprod, U.tensorInducedMulAlgHom_tprod]

/-- On a factor inclusion at coset `x`, `TensorInduced.mulAlgHom` acts by the chosen coset
representative. -/
@[simp↓]
theorem mulAlgHom_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    mulAlgHom U s R A (singleAlgHom x a) = U.leftTransversalRep s x • a := by
  rw [mulAlgHom_apply, toTensor_singleAlgHom, U.tensorInducedMulAlgHom_singleAlgHom]

/-- `TensorInduced.mulAlgHom` is `G`-equivariant. -/
@[simp]
theorem mulAlgHom_smul (g : G) (z : U.TensorInduced s R A) :
    mulAlgHom U s R A (g • z) = g • mulAlgHom U s R A z := by
  rw [mulAlgHom_apply, mulAlgHom_apply, toTensor_smul_group]
  exact U.tensorInducedMulAlgHom_tensorInducedAlgAut s R A g z.toTensor

/-- **Evens' twisted multiplication as a homomorphism of `G`-semirings** (`U.TensorInduced s R A`
to `A`). -/
noncomputable def mulSemiringActionHom : U.TensorInduced s R A →+*[G] A where
  __ := (mulAlgHom U s R A).toRingHom
  map_smul' := mulAlgHom_smul U s R A

/-- Evaluating `TensorInduced.mulSemiringActionHom` gives `TensorInduced.mulAlgHom`. -/
@[simp]
theorem mulSemiringActionHom_apply (z : U.TensorInduced s R A) :
    mulSemiringActionHom U s R A z = mulAlgHom U s R A z := (rfl)

/-- On a pure tensor, `TensorInduced.mulSemiringActionHom` twists each coset entry by its
transversal representative and multiplies the results in `A`. -/
theorem mulSemiringActionHom_tprod (m : G ⧸ U → A) :
    mulSemiringActionHom U s R A (tprod m) = ∏ x : G ⧸ U, U.leftTransversalRep s x • m x :=
  mulAlgHom_tprod U s R A m

/-- Precomposing `mulSemiringActionHom` with `changeTransversalMulSemiringActionHom` switches the
left transversal. -/
@[simp]
theorem mulSemiringActionHom_comp_changeTransversal (t : U.LeftTransversal) :
    (mulSemiringActionHom U s R A).comp (changeTransversalMulSemiringActionHom U R A s t) =
      mulSemiringActionHom U t R A := by
  ext z
  simp only [MulSemiringActionHom.comp_apply, changeTransversalMulSemiringActionHom_apply,
    mulSemiringActionHom_apply, mulAlgHom_apply, toTensor_changeTransversalAlgEquiv,
    tensorInducedMulAlgHom_changeTransversal]

end TensorInduced

end Multiplication

section MultiplicationTransitivity

variable {G : Type v} [Group G] {U V : Subgroup G} (hVU : V ≤ U)
  (s : U.LeftTransversal) (t : (V.subgroupOf U).LeftTransversal)
  [Fintype (G ⧸ U)] [Fintype (U ⧸ V.subgroupOf U)] [Fintype (G ⧸ V)]
  (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- **Transitivity of Evens' twisted multiplication along a subgroup tower `V ≤ U ≤ G`.**
Applying twisted multiplication from `V.subgroupOf U` to `U` in each outer factor and then twisted
multiplication from `U` to `G` equals flattening via `tensorInducedTransitivityAlgEquiv` followed
by twisted multiplication from `V` to `G` for `compositeLeftTransversal hVU s t`. -/
theorem tensorInducedMulAlgHom_transitivity :
    (U.tensorInducedMulAlgHom s R A).comp
        (PiTensorProduct.mapAlgHom fun _ : G ⧸ U ↦ (V.subgroupOf U).tensorInducedMulAlgHom t R A) =
      (V.tensorInducedMulAlgHom (compositeLeftTransversal hVU s t) R A).comp
        (tensorInducedTransitivityAlgEquiv hVU s R A).toAlgHom := by
  refine AlgHom.toLinearMap_injective <| PiTensorProduct.ext_sigma_tprod fun m ↦ ?_
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    PiTensorProduct.mapAlgHom_tprod, tensorInducedMulAlgHom_tprod,
    tensorInducedTransitivityAlgEquiv_tprod, leftTransversalRep_compositeLeftTransversal]
  let e := quotientEquivProdOfLE' hVU (U.leftTransversalRep s) (U.leftTransversalRep_mk s)
  rw [← e.symm.prod_comp]
  simp only [e, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hmap := (map_prod (MulSemiringAction.toRingHom G A (U.leftTransversalRep s a))
    (fun b : U ⧸ V.subgroupOf U ↦ (V.subgroupOf U).leftTransversalRep t b • m a b) Finset.univ)
  refine hmap.trans (Finset.prod_congr rfl fun b _ ↦ ?_)
  rw [MulSemiringAction.toRingHom_apply, Subgroup.smul_def, ← mul_smul,
    compositeTransversal_apply, Equiv.apply_symm_apply]

end MultiplicationTransitivity

end Subgroup

/-! ### Concrete checks for trivial and non-trivial `G`-actions -/

section Examples

open Polynomial

/-- Canonical left transversal `Set.univ` of the trivial subgroup `⊥` of `Multiplicative (ZMod 2)`.
-/
private def modTwoBotTransversal :
    (⊥ : Subgroup (Multiplicative (ZMod 2))).LeftTransversal :=
  ⟨Set.univ, Subgroup.isComplement'_top_bot⟩

/-- Canonical bijection `Fin 2 ≃ Multiplicative (ZMod 2) ⧸ ⊥`. -/
private noncomputable def modTwoBotQuotEquiv :
    Fin 2 ≃ Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2))) :=
  (ZMod.finEquiv 2).toEquiv.trans
    (Multiplicative.ofAdd.trans QuotientGroup.quotientBot.symm.toEquiv)

open scoped Classical in
/-- On `ℤ` with the trivial action of `Multiplicative (ZMod 2)` and `U = ⊥`, twisted
multiplication on `ℤ ⊗[ℤ] ℤ` sends `a ⊗ b` to `a * b` (in particular, `2 ⊗ 3 ↦ 6` and
`3 ⊗ 2 ↦ 6`). -/
private theorem modTwoTrivial_mul (a b : ℤ) :
    letI : MulSemiringAction (Multiplicative (ZMod 2)) ℤ :=
      MulSemiringAction.compHom ℤ
        { toFun := fun _ ↦ RingEquiv.refl ℤ, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    letI : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
      Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
    (⊥ : Subgroup (Multiplicative (ZMod 2))).tensorInducedMulAlgHom modTwoBotTransversal ℤ ℤ
      (PiTensorProduct.tprod ℤ fun q ↦
        if q = QuotientGroup.mk 1 then a else b) = a * b := by
  let _ : MulSemiringAction (Multiplicative (ZMod 2)) ℤ :=
    MulSemiringAction.compHom ℤ
      { toFun := fun _ ↦ RingEquiv.refl ℤ, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  let _ : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
    Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
  have htriv : ∀ (g : Multiplicative (ZMod 2)) (n : ℤ), g • n = n := fun _ _ ↦ rfl
  rw [Subgroup.tensorInducedMulAlgHom_tprod]
  simp_rw [htriv]
  rw [← modTwoBotQuotEquiv.prod_comp, Fin.prod_univ_two]
  have h0 : modTwoBotQuotEquiv 0 = QuotientGroup.mk 1 := by simp [modTwoBotQuotEquiv]
  have h1 : modTwoBotQuotEquiv 1 ≠ QuotientGroup.mk 1 := fun h ↦
    absurd (modTwoBotQuotEquiv.injective (h.trans h0.symm)) (by decide)
  rw [ite_eq_left h0, ite_eq_right h1]

open scoped Classical in
example :
    letI : MulSemiringAction (Multiplicative (ZMod 2)) ℤ :=
      MulSemiringAction.compHom ℤ
        { toFun := fun _ ↦ RingEquiv.refl ℤ, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    letI : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
      Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
    let μ :=
      (⊥ : Subgroup (Multiplicative (ZMod 2))).tensorInducedMulAlgHom modTwoBotTransversal ℤ ℤ
    μ (PiTensorProduct.tprod ℤ fun q ↦ if q = QuotientGroup.mk 1 then 2 else 3) = 6 ∧
      μ (PiTensorProduct.tprod ℤ fun q ↦ if q = QuotientGroup.mk 1 then 3 else 2) = 6 :=
  ⟨modTwoTrivial_mul 2 3, modTwoTrivial_mul 3 2⟩

/-- Group homomorphism `Multiplicative (ZMod 2) →* (ℤ[X] ≃ₐ[ℤ] ℤ[X])` acting by `X ↦ -X`. -/
private noncomputable def polyNegXAut :
    Multiplicative (ZMod 2) →* (Polynomial ℤ ≃ₐ[ℤ] Polynomial ℤ) where
  toFun g := Polynomial.algEquivAevalNegX (R := ℤ) ^ g.toAdd.val
  map_one' := rfl
  map_mul' g h := by
    have hsq : Polynomial.algEquivAevalNegX (R := ℤ) ^ 2 = 1 := by
      rw [sq]
      exact AlgEquiv.ext fun p ↦ by
        simp only [AlgEquiv.mul_apply, algEquivAevalNegX_apply, ← comp_eq_aeval,
          comp_neg_X_comp_neg_X, AlgEquiv.one_apply]
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    nth_rw 2 [← Nat.div_add_mod (g.toAdd.val + h.toAdd.val) 2]
    rw [pow_add, pow_mul, hsq, one_pow, one_mul]

private theorem polyNegXAut_apply (g : Multiplicative (ZMod 2)) :
    polyNegXAut g = Polynomial.algEquivAevalNegX (R := ℤ) ^ g.toAdd.val :=
  rfl

open scoped Classical in
/-- On `A = ℤ[X]` with `G = Multiplicative (ZMod 2)` acting by `X ↦ -X` and `U = ⊥`, Evens'
twisted multiplication sends `p(X) ⊗ q(X)` to `p(X) * q(-X)`. -/
private theorem modTwoPoly_mul (p q : Polynomial ℤ) :
    letI : MulSemiringAction (Multiplicative (ZMod 2)) (Polynomial ℤ) :=
      MulSemiringAction.compHom _ polyNegXAut
    letI : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
      Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
    (⊥ : Subgroup (Multiplicative (ZMod 2))).tensorInducedMulAlgHom modTwoBotTransversal ℤ
      (Polynomial ℤ)
      (PiTensorProduct.tprod ℤ fun c ↦
        if c = QuotientGroup.mk 1 then p else q) =
      p * aeval (-X : Polynomial ℤ) q := by
  let _ : MulSemiringAction (Multiplicative (ZMod 2)) (Polynomial ℤ) :=
    MulSemiringAction.compHom _ polyNegXAut
  let _ : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
    Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
  let σ : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
  rw [Subgroup.tensorInducedMulAlgHom_tprod, ← modTwoBotQuotEquiv.prod_comp, Fin.prod_univ_two]
  have he0 : modTwoBotQuotEquiv 0 = QuotientGroup.mk 1 := by simp [modTwoBotQuotEquiv]
  have he1 : modTwoBotQuotEquiv 1 = QuotientGroup.mk σ := by simp [modTwoBotQuotEquiv, σ]
  have hσne : modTwoBotQuotEquiv 1 ≠ QuotientGroup.mk 1 := fun h ↦
    absurd (modTwoBotQuotEquiv.injective (h.trans he0.symm)) (by decide)
  have hrep1 : (⊥ : Subgroup (Multiplicative (ZMod 2))).leftTransversalRep modTwoBotTransversal
      (QuotientGroup.mk 1) = 1 :=
    Subgroup.leftTransversalRep_mk_of_mem _ modTwoBotTransversal (Set.mem_univ 1)
  have hrepσ : (⊥ : Subgroup (Multiplicative (ZMod 2))).leftTransversalRep modTwoBotTransversal
      (QuotientGroup.mk σ) = σ :=
    Subgroup.leftTransversalRep_mk_of_mem _ modTwoBotTransversal (Set.mem_univ σ)
  rw [ite_eq_left he0, ite_eq_right hσne, he0, he1, hrep1, hrepσ, one_smul]
  have hσ : σ • q = aeval (-X : Polynomial ℤ) q := by
    rw [MulAction.compHom_smul_def, polyNegXAut_apply]
    have hval : σ.toAdd.val = 1 := rfl
    rw [hval, pow_one]
    exact Polynomial.algEquivAevalNegX_apply q
  rw [hσ]

open scoped Classical in
/-- Concrete check on `ℤ[X]` with `X ↦ -X`: Evens' twisted multiplication sends `X ⊗ 1` to `X`
and `1 ⊗ X` to `-X`, and swapping the tensor factors by the generator `σ` agrees with `σ` acting
on the target. -/
example :
    letI : MulSemiringAction (Multiplicative (ZMod 2)) (Polynomial ℤ) :=
      MulSemiringAction.compHom _ polyNegXAut
    letI : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
      Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
    let μ := (⊥ : Subgroup (Multiplicative (ZMod 2))).tensorInducedMulAlgHom
      modTwoBotTransversal ℤ (Polynomial ℤ)
    let z₁ := PiTensorProduct.tprod ℤ
      (fun c ↦ if c = QuotientGroup.mk 1 then (X : Polynomial ℤ) else 1)
    let z₂ := PiTensorProduct.tprod ℤ
      (fun c ↦ if c = QuotientGroup.mk 1 then (1 : Polynomial ℤ) else X)
    let σ : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
    μ z₁ = X ∧ μ z₂ = -X ∧
      μ ((⊥ : Subgroup (Multiplicative (ZMod 2))).tensorInducedAlgAut
        modTwoBotTransversal ℤ (Polynomial ℤ) σ z₁) = σ • μ z₁ := by
  let _ : MulSemiringAction (Multiplicative (ZMod 2)) (Polynomial ℤ) :=
    MulSemiringAction.compHom _ polyNegXAut
  let _ : Fintype (Multiplicative (ZMod 2) ⧸ (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
    Fintype.ofEquiv (Fin 2) modTwoBotQuotEquiv
  refine ⟨by simpa using modTwoPoly_mul X 1, by simpa using modTwoPoly_mul 1 X, ?_⟩
  exact Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut _ modTwoBotTransversal ℤ
    (Polynomial ℤ) (Multiplicative.ofAdd 1) _

end Examples
