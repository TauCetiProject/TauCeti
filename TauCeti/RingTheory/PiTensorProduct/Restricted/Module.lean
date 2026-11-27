/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PiTensorProduct.Restricted

/-!
# The action of a restricted tensor product algebra on a restricted tensor product of modules

Let `A i` be nonunital algebras over a commutative semiring `R` with idempotents `e i`, and
`ρ i : A i →ₙₐ[R] Module.End R (M i)` actions of the `A i` on `R`-modules `M i`, with reference
vectors `m i` fixed by the idempotents, `ρ i (e i) (m i) = m i`. On a finite stage `S` the tensor
product `⨂_{i ∈ S} A i` acts on `⨂_{i ∈ S} M i` factorwise
(`TauCeti.RestrictedTensor.stageAction`). Adjoining the idempotents and the references commutes
with these actions, because `e i` fixes `m i`
(`TauCeti.RestrictedTensor.stageAction_stageMap_stageMap`), so the actions glue to an action of
the restricted tensor product algebra `TauCeti.RestrictedTensorAlgebra R A e he` on the restricted
tensor product `TauCeti.RestrictedTensor R M m`
(`TauCeti.RestrictedTensorAlgebra.action`). An element of the stage `S` acts on an element of
the stage `T` at any common stage `U ⊇ S ∪ T`
(`TauCeti.RestrictedTensorAlgebra.action_ofFinite_ofFinite`), and restricted pure tensors act
factorwise (`TauCeti.RestrictedTensorAlgebra.action_tprod_tprod`).

## Main definitions

* `TauCeti.RestrictedTensor.stageAction`: the factorwise action on a finite stage.
* `TauCeti.RestrictedTensorAlgebra.action`: the action of the restricted tensor product algebra
  on the restricted tensor product of modules, as a morphism of nonunital algebras to
  `Module.End R (RestrictedTensor R M m)`.

## Main results

* `TauCeti.RestrictedTensor.stageAction_mul`: the finite-stage action is multiplicative.
* `TauCeti.RestrictedTensor.stageAction_stageMap_stageMap`: adjoining idempotents and references
  commutes with the finite-stage actions.
* `TauCeti.RestrictedTensorAlgebra.action_ofFinite_ofFinite`: the action is computed at a common
  finite stage.
* `TauCeti.RestrictedTensorAlgebra.action_tprod_tprod`: restricted pure tensors act factorwise.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R] {A : ι → Type*}
  [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)]
  [∀ i, IsScalarTower R (A i) (A i)] {e : ∀ i, A i}
  {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  (ρ : ∀ i, A i →ₙₐ[R] Module.End R (M i)) {m : ∀ i, M i}

namespace RestrictedTensor

omit [DecidableEq ι] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)] in
/-- The factorwise action of `⨂_{i ∈ S} A i` on `⨂_{i ∈ S} M i`. -/
def stageAction (S : Finset ι) : (⨂[R] i : S, A i) →ₗ[R] Module.End R (⨂[R] i : S, M i) :=
  PiTensorProduct.piTensorHomMap ∘ₗ PiTensorProduct.map fun i : S ↦ (ρ i : A i →ₗ[R] _)

omit [DecidableEq ι] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)] in
/-- The finite-stage action on pure tensors is factorwise. -/
@[simp]
theorem stageAction_tprod_tprod (S : Finset ι) (a : ∀ i : S, A i) (v : ∀ i : S, M i) :
    stageAction ρ S (⨂ₜ[R] i, a i) (⨂ₜ[R] i, v i) = ⨂ₜ[R] i : S, ρ i (a i) (v i) := by
  simp [stageAction]

omit [DecidableEq ι] in
/-- **The finite-stage action is multiplicative.** -/
theorem stageAction_mul (S : Finset ι) (x y : ⨂[R] i : S, A i) :
    stageAction ρ S (x * y) = stageAction ρ S x * stageAction ρ S y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s b =>
      refine PiTensorProduct.ext (MultilinearMap.ext fun v ↦ ?_)
      simp [smul_mul_smul_comm, PiTensorProduct.tprod_mul_tprod, mul_apply_eq_comp, map_smul,
        mul_comm r s, mul_smul]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

variable {ρ}

/-- **Adjoining idempotents and references commutes with the finite-stage actions**, because each
idempotent `e i` fixes the reference `m i`. -/
theorem stageAction_stageMap_stageMap (hρ : ∀ i, ρ i (e i) (m i) = m i) {S T : Finset ι}
    (h : S ⊆ T) (x : ⨂[R] i : S, A i) (y : ⨂[R] i : S, M i) :
    stageAction ρ T (stageMap R e h x) (stageMap R m h y) =
      stageMap R m h (stageAction ρ S x y) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s v =>
      simp only [map_smul, LinearMap.smul_apply, stageMap_tprod, stageAction_tprod_tprod]
      congr 3
      funext i
      by_cases hi : (i : ι) ∈ S
      · simp [Finset.restrict, Function.updateFinset_apply_of_mem hi]
      · simp [Finset.restrict, Function.updateFinset_apply_of_notMem hi, hρ]
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
  | add x x' hx hx' => rw [map_add, map_add, LinearMap.add_apply, hx, hx', map_add,
      LinearMap.add_apply, map_add]

/-- Moving the factorwise action of `x` from the stage `S` on `y` from the stage `T` up from a
common stage `V` to a larger stage `U` does not change it in the restricted tensor product. -/
private theorem ofFinite_stageAction_stageMap (hρ : ∀ i, ρ i (e i) (m i) = m i)
    {S T U V : Finset ι} (hVU : V ⊆ U) (hSV : S ⊆ V) (hTV : T ⊆ V) (hSU : S ⊆ U) (hTU : T ⊆ U)
    (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, M i) :
    ofFinite R M m V (stageAction ρ V (stageMap R e hSV x) (stageMap R m hTV y)) =
      ofFinite R M m U (stageAction ρ U (stageMap R e hSU x) (stageMap R m hTU y)) := by
  rw [← ofFinite_stageMap hVU, ← stageAction_stageMap_stageMap hρ hVU, stageMap_stageMap,
    stageMap_stageMap]

variable (m) in
/-- The action of an element `x` of the stage `S` on the restricted tensor product: on the stage
`T` it acts at the stage `S ∪ T`. -/
private def stageEndAux (hρ : ∀ i, ρ i (e i) (m i) = m i) (S : Finset ι) (x : ⨂[R] i : S, A i) :
    RestrictedTensor R M m →ₗ[R] RestrictedTensor R M m :=
  lift (fun T ↦ ofFinite R M m (S ∪ T) ∘ₗ
      stageAction ρ (S ∪ T) (stageMap R e Finset.subset_union_left x) ∘ₗ
        stageMap R m Finset.subset_union_right) fun T T' h y ↦ by
    simp only [LinearMap.coe_comp, Function.comp_apply, stageMap_stageMap]
    exact (ofFinite_stageAction_stageMap hρ (Finset.union_subset_union_right h) _ _ _ _ x y).symm

/-- The action of `x` from the stage `S` on an element of the stage `T` is computed at any common
stage `U ⊇ S ∪ T`. -/
private theorem stageEndAux_ofFinite (hρ : ∀ i, ρ i (e i) (m i) = m i) {S T U : Finset ι}
    (hS : S ⊆ U) (hT : T ⊆ U) (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, M i) :
    stageEndAux m hρ S x (ofFinite R M m T y) =
      ofFinite R M m U (stageAction ρ U (stageMap R e hS x) (stageMap R m hT y)) := by
  rw [stageEndAux, lift_ofFinite, LinearMap.comp_apply, LinearMap.comp_apply,
    ofFinite_stageAction_stageMap hρ (Finset.union_subset hS hT) _ _ hS hT]

variable (m) in
/-- The action of the stage `S` on the restricted tensor product, as a morphism of nonunital
algebras. -/
private def stageEnd (he : ∀ i, IsIdempotentElem (e i)) (hρ : ∀ i, ρ i (e i) (m i) = m i)
    (S : Finset ι) : (⨂[R] i : S, A i) →ₙₐ[R] Module.End R (RestrictedTensor R M m) where
  toFun := stageEndAux m hρ S
  map_smul' c x := hom_ext fun T ↦ LinearMap.ext fun y ↦ by
    simp [stageEndAux_ofFinite hρ Finset.subset_union_left Finset.subset_union_right]
  map_zero' := hom_ext fun T ↦ LinearMap.ext fun y ↦ by
    simp [stageEndAux_ofFinite hρ Finset.subset_union_left Finset.subset_union_right]
  map_add' x x' := hom_ext fun T ↦ LinearMap.ext fun y ↦ by
    simp [stageEndAux_ofFinite hρ Finset.subset_union_left Finset.subset_union_right]
  map_mul' x x' := hom_ext fun T ↦ LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mul_apply_eq_comp,
      stageEndAux_ofFinite hρ Finset.subset_union_left Finset.subset_union_right x',
      stageEndAux_ofFinite hρ Finset.subset_union_left (subset_refl _) x,
      stageEndAux_ofFinite hρ Finset.subset_union_left Finset.subset_union_right, stageMap_self,
      stageMap_mul he, stageAction_mul, mul_apply_eq_comp]

/-- The action of `x` from the stage `S` on an element of the stage `T` is computed at any common
stage `U ⊇ S ∪ T`. -/
private theorem stageEnd_ofFinite (he : ∀ i, IsIdempotentElem (e i))
    (hρ : ∀ i, ρ i (e i) (m i) = m i) {S T U : Finset ι} (hS : S ⊆ U) (hT : T ⊆ U)
    (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, M i) :
    stageEnd m he hρ S x (ofFinite R M m T y) =
      ofFinite R M m U (stageAction ρ U (stageMap R e hS x) (stageMap R m hT y)) :=
  stageEndAux_ofFinite hρ hS hT x y

omit [DecidableEq ι] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)] in
/-- The factorwise action `ρ i (a i) (v i)` differs from the reference `m i` only where
`a i ≠ e i` or `v i ≠ m i`, because each idempotent `e i` fixes `m i`. -/
theorem setOf_apply_ne_subset_union (hρ : ∀ i, ρ i (e i) (m i) = m i) (a : ∀ i, A i)
    (v : ∀ i, M i) : {i | ρ i (a i) (v i) ≠ m i} ⊆ {i | a i ≠ e i} ∪ {i | v i ≠ m i} :=
  fun i hi ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hi (by rw [h.1, h.2, hρ])

end RestrictedTensor

open RestrictedTensor

namespace RestrictedTensorAlgebra

variable (m) in
/-- **The action of the restricted tensor product algebra on the restricted tensor product of
modules.** If `ρ i : A i →ₙₐ[R] Module.End R (M i)` and each idempotent `e i` fixes the reference
`m i`, then `⨂' A i` acts on `⨂' M i`, an element of the stage `S` acting on an element of the
stage `T` factorwise at the stage `S ∪ T`. -/
def action (he : ∀ i, IsIdempotentElem (e i)) (hρ : ∀ i, ρ i (e i) (m i) = m i) :
    RestrictedTensorAlgebra R A e he →ₙₐ[R] Module.End R (RestrictedTensor R M m) :=
  lift he (stageEnd m he hρ) fun S T h x ↦ RestrictedTensor.hom_ext fun V ↦ LinearMap.ext fun y ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      stageEnd_ofFinite he hρ (Finset.subset_union_left : T ⊆ T ∪ V)
        (Finset.subset_union_right : V ⊆ T ∪ V),
      stageEnd_ofFinite he hρ (h.trans Finset.subset_union_left)
        (Finset.subset_union_right : V ⊆ T ∪ V), stageMap_stageMap]

variable {ρ} {he : ∀ i, IsIdempotentElem (e i)}

/-- **The action is computed at a common finite stage**: an element of the stage `S` acts on an
element of the stage `T` through the factorwise action at any stage `U ⊇ S ∪ T`. -/
theorem action_ofFinite_ofFinite (hρ : ∀ i, ρ i (e i) (m i) = m i) {S T U : Finset ι}
    (hS : S ⊆ U) (hT : T ⊆ U) (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, M i) :
    action ρ m he hρ (ofFinite he S x) (RestrictedTensor.ofFinite R M m T y) =
      RestrictedTensor.ofFinite R M m U
        (stageAction ρ U (stageMap R e hS x) (stageMap R m hT y)) := by
  rw [action, lift_ofFinite, stageEnd_ofFinite he hρ hS hT]

/-- **Restricted pure tensors act factorwise**: `(⨂ a i) • (⨂ v i) = ⨂ ρ i (a i) (v i)`. -/
@[simp]
theorem action_tprod_tprod (hρ : ∀ i, ρ i (e i) (m i) = m i) (a : ∀ i, A i)
    (ha : {i | a i ≠ e i}.Finite) (v : ∀ i, M i) (hv : {i | v i ≠ m i}.Finite) :
    action ρ m he hρ (tprod R he a ha) (RestrictedTensor.tprod R m v hv) =
      RestrictedTensor.tprod R m (fun i ↦ ρ i (a i) (v i))
        ((ha.union hv).subset (setOf_apply_ne_subset_union hρ a v)) := by
  have haS : ∀ i ∉ ha.toFinset ∪ hv.toFinset, a i = e i := fun i hi ↦ by
    simpa using (Finset.notMem_union.mp hi).1
  have hvS : ∀ i ∉ ha.toFinset ∪ hv.toFinset, v i = m i := fun i hi ↦ by
    simpa using (Finset.notMem_union.mp hi).2
  rw [tprod_eq_ofFinite a ha _ haS, RestrictedTensor.tprod_eq_ofFinite v hv _ hvS,
    action_ofFinite_ofFinite hρ (subset_refl _) (subset_refl _), stageMap_self, stageMap_self,
    stageAction_tprod_tprod,
    RestrictedTensor.tprod_eq_ofFinite _ _ (ha.toFinset ∪ hv.toFinset) fun i hi ↦ not_not.mp
      fun h ↦ hi (by simpa using setOf_apply_ne_subset_union hρ a v h)]

end RestrictedTensorAlgebra

end TauCeti
