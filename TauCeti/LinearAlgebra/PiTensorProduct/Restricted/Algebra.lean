/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.LinearAlgebra.PiTensorProduct.Restricted

/-!
# Restricted tensor products of algebras stabilized by idempotents

Let `A i` be algebras over a commutative semiring `R`, indexed by a possibly infinite type `ι`,
and `e i ∈ A i` idempotents. Adjoining the idempotents at the places of `T \ S` is multiplicative,
`(x ⊗ e) (y ⊗ e) = x y ⊗ e e = x y ⊗ e`, because the `e i` are idempotent (they need not be units),
so the transition maps `TauCeti.RestrictedTensor.stageMap R e` of the restricted tensor product
are morphisms of nonunital algebras between the finite tensor products `⨂_{i ∈ S} A i`. Their
direct limit `TauCeti.RestrictedTensorAlgebra R A e he` is a nonunital `R`-algebra, the
**restricted tensor product of the `A i` stabilized by the `e i`**: the product of two elements
is computed at a common finite stage (`TauCeti.RestrictedTensorAlgebra.ofFinite_mul_ofFinite`). As
a module it is the restricted tensor product `TauCeti.RestrictedTensor R A e`
(`TauCeti.RestrictedTensorAlgebra.linearEquiv`).

## Main definitions

* `TauCeti.RestrictedTensor.stageNonUnitalAlgHom`: the transition map as a morphism of nonunital
  algebras.
* `TauCeti.RestrictedTensorAlgebra R A e he`: the restricted tensor product algebra.
* `TauCeti.RestrictedTensorAlgebra.ofFinite`: the inclusion of a finite stage.
* `TauCeti.RestrictedTensorAlgebra.linearEquiv`: the identification with
  `TauCeti.RestrictedTensor R A e` as modules.

## Main results

* `TauCeti.RestrictedTensor.stageMap_mul`: adjoining idempotents is multiplicative.
* `TauCeti.RestrictedTensorAlgebra.ofFinite_mul_ofFinite`: products are computed at a common finite
  stage.
* `TauCeti.RestrictedTensorAlgebra.linearEquiv_ofFinite`: the identification on finite stages.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommSemiring R] (A : ι → Type*)
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] (e : ∀ i, A i)

namespace RestrictedTensor

variable {R A e}

/-- **Adjoining idempotents is multiplicative.** If every `e i` is idempotent, the transition map
adjoining the `e i` at the places of `T \ S` preserves products. -/
theorem stageMap_mul (he : ∀ i, IsIdempotentElem (e i)) {S T : Finset ι} (h : S ⊆ T)
    (x y : ⨂[R] i : S, A i) :
    stageMap R e h (x * y) = stageMap R e h x * stageMap R e h y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s g =>
      rw [smul_mul_smul_comm, PiTensorProduct.tprod_mul_tprod, map_smul, map_smul, map_smul,
        stageMap_tprod, stageMap_tprod, stageMap_tprod, smul_mul_smul_comm,
        PiTensorProduct.tprod_mul_tprod]
      congr 2
      funext i
      by_cases hi : (i : ι) ∈ S
      · simp [Finset.restrict, Function.updateFinset_apply_of_mem hi]
      · simp [Finset.restrict, Function.updateFinset_apply_of_notMem hi, (he i).eq]
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]

variable (R e) in
/-- The transition map adjoining idempotents, as a morphism of nonunital algebras. -/
def stageNonUnitalAlgHom (he : ∀ i, IsIdempotentElem (e i)) {S T : Finset ι} (h : S ⊆ T) :
    (⨂[R] i : S, A i) →ₙₐ[R] ⨂[R] i : T, A i where
  toFun := stageMap R e h
  map_smul' := (stageMap R e h).map_smul
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' := stageMap_mul he h

@[simp]
theorem coe_stageNonUnitalAlgHom (he : ∀ i, IsIdempotentElem (e i)) {S T : Finset ι}
    (h : S ⊆ T) : ⇑(stageNonUnitalAlgHom R e he h) = stageMap R e h :=
  (rfl)

/-- The finite tensor products of the `A i`, with the transition maps adjoining idempotents, form
a directed system of nonunital algebras. -/
instance directedSystemStageNonUnitalAlgHom (he : ∀ i, IsIdempotentElem (e i)) :
    DirectedSystem (fun S : Finset ι ↦ ⨂[R] i : S, A i)
      (fun _ _ h ↦ ⇑(stageNonUnitalAlgHom R e he h)) where
  map_self S x := by
    rw [coe_stageNonUnitalAlgHom]
    exact stageMap_self (R := R) e S x
  map_map _ _ _ hST hTU x := by
    simp only [coe_stageNonUnitalAlgHom]
    exact stageMap_stageMap (R := R) e hST hTU x

end RestrictedTensor

open RestrictedTensor

/-- The **restricted tensor product of algebras stabilized by idempotents**: the direct limit, over
finite sets `S` of indices, of the algebras `⨂_{i ∈ S} A i` along the multiplicative maps adjoining
the idempotents `e i`. It is reducible to the direct limit, whose algebraic structure it
inherits. -/
abbrev RestrictedTensorAlgebra (he : ∀ i, IsIdempotentElem (e i)) : Type _ :=
  DirectLimit (fun S : Finset ι ↦ ⨂[R] i : S, A i) fun _ _ h ↦ stageNonUnitalAlgHom R e he h

namespace RestrictedTensorAlgebra

variable {R A e} (he : ∀ i, IsIdempotentElem (e i))

/-- The inclusion of the finite stage `S`, a morphism of nonunital algebras. -/
def ofFinite (S : Finset ι) : (⨂[R] i : S, A i) →ₙₐ[R] RestrictedTensorAlgebra R A e he :=
  DirectLimit.NonUnitalAlgebra.of (fun S : Finset ι ↦ ⨂[R] i : S, A i)
    (fun _ _ h ↦ stageNonUnitalAlgHom R e he h) S

/-- The inclusion of a finite stage, as a linear map, is the inclusion into the direct limit of
modules. -/
theorem ofFinite_apply (S : Finset ι) (x : ⨂[R] i : S, A i) :
    ofFinite he S x = DirectLimit.Module.of R (Finset ι) (fun S : Finset ι ↦ ⨂[R] i : S, A i)
      (fun _ _ h ↦ stageNonUnitalAlgHom R e he h) S x :=
  (rfl)

variable {he}

/-- The finite-stage inclusions are compatible with the transition maps. -/
@[simp]
theorem ofFinite_stageMap {S T : Finset ι} (h : S ⊆ T) (x : ⨂[R] i : S, A i) :
    ofFinite he T (stageMap R e h x) = ofFinite he S x :=
  DirectLimit.NonUnitalAlgebra.of_f (G := fun S : Finset ι ↦ ⨂[R] i : S, A i)
    (f := fun _ _ h ↦ stageNonUnitalAlgHom R e he h) h x

/-- Every element comes from a finite stage. -/
theorem exists_ofFinite (z : RestrictedTensorAlgebra R A e he) :
    ∃ (S : Finset ι) (x : ⨂[R] i : S, A i), ofFinite he S x = z :=
  DirectLimit.induction (C := fun z ↦ ∃ (S : Finset ι) (x : ⨂[R] i : S, A i), ofFinite he S x = z)
    _ (fun S x ↦ ⟨S, x, rfl⟩) z

/-- **Products are computed at a common finite stage.** -/
theorem ofFinite_mul_ofFinite {S T : Finset ι} (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, A i) :
    ofFinite he S x * ofFinite he T y =
      ofFinite he (S ∪ T)
        (stageMap R e Finset.subset_union_left x * stageMap R e Finset.subset_union_right y) := by
  rw [map_mul, ofFinite_stageMap, ofFinite_stageMap]

variable (he) in
/-- As a module, the restricted tensor product algebra is the restricted tensor product of the
`A i` with reference vectors `e i`. -/
def linearEquiv : RestrictedTensorAlgebra R A e he ≃ₗ[R] RestrictedTensor R A e :=
  LinearEquiv.ofLinearMap
    (DirectLimit.Module.lift R (Finset ι) _ _ (fun S ↦ RestrictedTensor.ofFinite R A e S)
      fun _ _ h x ↦ by
        rw [coe_stageNonUnitalAlgHom]
        exact RestrictedTensor.ofFinite_stageMap (R := R) (W := A) (w := e) h x)
    (RestrictedTensor.lift (fun S ↦ LinearMap.ofClass (ofFinite he S)) fun _ _ h x ↦ by
      rw [LinearMap.coe_ofClass, LinearMap.coe_ofClass]
      exact ofFinite_stageMap h x)
    (RestrictedTensor.hom_ext fun S ↦ LinearMap.ext fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        RestrictedTensor.lift_ofFinite (R := R) (W := A) (w := e), LinearMap.coe_ofClass,
        ofFinite_apply, DirectLimit.Module.lift_of]
      rfl)
    (DirectLimit.Module.hom_ext fun S ↦ LinearMap.ext fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        DirectLimit.Module.lift_of, RestrictedTensor.lift_ofFinite (R := R) (W := A) (w := e),
        LinearMap.coe_ofClass, ofFinite_apply, LinearMap.id_apply])

/-- The identification with the restricted tensor product on finite stages. -/
@[simp]
theorem linearEquiv_ofFinite (S : Finset ι) (x : ⨂[R] i : S, A i) :
    linearEquiv he (ofFinite he S x) = RestrictedTensor.ofFinite R A e S x := by
  rfl

/-- The inverse identification on finite stages. -/
@[simp]
theorem linearEquiv_symm_ofFinite (S : Finset ι) (x : ⨂[R] i : S, A i) :
    (linearEquiv he).symm (RestrictedTensor.ofFinite R A e S x) = ofFinite he S x :=
  RestrictedTensor.lift_ofFinite (R := R) (W := A) (w := e) _ _ S x

end RestrictedTensorAlgebra

end TauCeti
