/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import TauCeti.LinearAlgebra.PiTensorProduct.Restricted
public import TauCeti.RingTheory.PiTensorProduct.Basic

/-!
# Restricted tensor products of algebras stabilized by idempotents

Let `A i` be nonunital, not necessarily associative, algebras over a commutative semiring `R`,
indexed by a possibly infinite type `ι`, and `e i ∈ A i` idempotents. Adjoining the idempotents at
the places of `T \ S` is multiplicative, `(x ⊗ e) (y ⊗ e) = x y ⊗ e e = x y ⊗ e`, because the
`e i` are idempotent (they need not be units), so the transition maps
`TauCeti.RestrictedTensor.stageMap R e` of the restricted tensor product are morphisms of nonunital
algebras between the finite tensor products `⨂_{i ∈ S} A i`. Their direct limit
`TauCeti.RestrictedTensorAlgebra R A e he` is a nonunital `R`-algebra, the **restricted tensor
product of the `A i` stabilized by the `e i`**: the product of two elements is computed at a common
finite stage (`TauCeti.RestrictedTensorAlgebra.ofFinite_mul_ofFinite`), where pure tensors multiply
factorwise (`TauCeti.RestrictedTensorAlgebra.ofFinite_tprod_mul_ofFinite_tprod`). As a module it is
the restricted tensor product `TauCeti.RestrictedTensor R A e`
(`TauCeti.RestrictedTensorAlgebra.linearEquiv`). Morphisms of nonunital algebras out of it
correspond to compatible morphisms out of the finite stages
(`TauCeti.RestrictedTensorAlgebra.lift`). When the `A i` are associative, so is the product.

## Main definitions

* `TauCeti.RestrictedTensor.stageNonUnitalAlgHom`: the transition map as a morphism of nonunital
  algebras.
* `TauCeti.RestrictedTensorAlgebra R A e he`: the restricted tensor product algebra.
* `TauCeti.RestrictedTensorAlgebra.ofFinite`: the inclusion of a finite stage.
* `TauCeti.RestrictedTensorAlgebra.lift`: the universal property.
* `TauCeti.RestrictedTensorAlgebra.linearEquiv`: the identification with
  `TauCeti.RestrictedTensor R A e` as modules.

## Main results

* `TauCeti.RestrictedTensor.stageMap_mul`: adjoining idempotents is multiplicative.
* `TauCeti.RestrictedTensorAlgebra.ofFinite_mul_ofFinite`: products are computed at a common finite
  stage.
* `TauCeti.RestrictedTensorAlgebra.ofFinite_eq_ofFinite_iff`: equality is detected at a common
  finite stage.
* `TauCeti.RestrictedTensorAlgebra.linearEquiv_ofFinite`: the identification on finite stages.
* `TauCeti.RestrictedTensorAlgebra.linearEquiv_symm_tprod_mul_linearEquiv_symm_tprod`: restricted
  pure tensors multiply factorwise.

## References

* D. Flath, *Decomposition of representations into tensor products*, in *Automorphic forms,
  representations and L-functions*, Proc. Sympos. Pure Math. **33**, Part 1 (1979), §2.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti

variable {ι : Type*} [DecidableEq ι] (R : Type*) [CommSemiring R] (A : ι → Type*)
  [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)]
  [∀ i, IsScalarTower R (A i) (A i)] (e : ∀ i, A i)

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
      simp only [smul_mul_smul_comm, PiTensorProduct.tprod_mul_tprod, map_smul, stageMap_tprod]
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

/-- Pure tensors at a finite stage multiply factorwise. -/
@[simp]
theorem ofFinite_tprod_mul_ofFinite_tprod (S : Finset ι) (f g : ∀ i : S, A i) :
    ofFinite he S (⨂ₜ[R] i, f i) * ofFinite he S (⨂ₜ[R] i, g i) =
      ofFinite he S (⨂ₜ[R] i, (f * g) i) := by
  rw [← map_mul, PiTensorProduct.tprod_mul_tprod]

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
      simp [ofFinite_apply])
    (DirectLimit.Module.hom_ext fun S ↦ LinearMap.ext fun x ↦ by
      simp [ofFinite_apply])

/-- The identification with the restricted tensor product on finite stages. -/
@[simp]
theorem linearEquiv_ofFinite (S : Finset ι) (x : ⨂[R] i : S, A i) :
    linearEquiv he (ofFinite he S x) = RestrictedTensor.ofFinite R A e S x := by
  rw [linearEquiv, LinearEquiv.coe_ofLinearMap, ofFinite_apply, DirectLimit.Module.lift_of]

/-- The inverse identification on finite stages. -/
@[simp]
theorem linearEquiv_symm_ofFinite (S : Finset ι) (x : ⨂[R] i : S, A i) :
    (linearEquiv he).symm (RestrictedTensor.ofFinite R A e S x) = ofFinite he S x := by
  rw [linearEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    RestrictedTensor.lift_ofFinite, LinearMap.coe_ofClass]

/-- Two elements of finite stages are equal in the restricted tensor product algebra exactly when
they agree after adjoining idempotents up to a common larger stage. -/
theorem ofFinite_eq_ofFinite_iff {S T : Finset ι} (x : ⨂[R] i : S, A i) (y : ⨂[R] i : T, A i) :
    ofFinite he S x = ofFinite he T y ↔
      ∃ (U : Finset ι) (hSU : S ⊆ U) (hTU : T ⊆ U), stageMap R e hSU x = stageMap R e hTU y := by
  rw [← (linearEquiv he).injective.eq_iff, linearEquiv_ofFinite, linearEquiv_ofFinite,
    RestrictedTensor.ofFinite_eq_ofFinite_iff]

/-- **Restricted pure tensors multiply factorwise**: `(⨂ f i) (⨂ g i) = ⨂ f i g i`. -/
theorem linearEquiv_symm_tprod_mul_linearEquiv_symm_tprod (f g : ∀ i, A i)
    (hf : {i | f i ≠ e i}.Finite) (hg : {i | g i ≠ e i}.Finite)
    (hfg : {i | (f * g) i ≠ e i}.Finite) :
    (linearEquiv he).symm (RestrictedTensor.tprod R e f hf) *
        (linearEquiv he).symm (RestrictedTensor.tprod R e g hg) =
      (linearEquiv he).symm (RestrictedTensor.tprod R e (f * g) hfg) := by
  have hfS : ∀ i ∉ hf.toFinset ∪ hg.toFinset, f i = e i := fun i hi ↦ by
    simpa using (Finset.notMem_union.mp hi).1
  have hgS : ∀ i ∉ hf.toFinset ∪ hg.toFinset, g i = e i := fun i hi ↦ by
    simpa using (Finset.notMem_union.mp hi).2
  rw [RestrictedTensor.tprod_eq_ofFinite f hf _ hfS, RestrictedTensor.tprod_eq_ofFinite g hg _ hgS,
    RestrictedTensor.tprod_eq_ofFinite (f * g) hfg _ fun i hi ↦ by
      rw [Pi.mul_apply, hfS i hi, hgS i hi, (he i).eq],
    linearEquiv_symm_ofFinite, linearEquiv_symm_ofFinite, linearEquiv_symm_ofFinite,
    ofFinite_tprod_mul_ofFinite_tprod]
  simp only [Pi.mul_apply]

section lift

variable {P : Type*} [NonUnitalNonAssocSemiring P] [DistribMulAction R P]

/-- Two morphisms of nonunital algebras out of the restricted tensor product algebra agreeing on
every finite stage are equal. -/
@[ext]
theorem hom_ext {g₁ g₂ : RestrictedTensorAlgebra R A e he →ₙₐ[R] P}
    (h : ∀ S, g₁.comp (ofFinite he S) = g₂.comp (ofFinite he S)) : g₁ = g₂ :=
  DirectLimit.NonUnitalAlgebra.hom_ext _ h

variable (he) in
/-- The morphism of nonunital algebras out of the restricted tensor product algebra induced by
compatible morphisms out of the finite stages. -/
def lift (g : ∀ S : Finset ι, (⨂[R] i : S, A i) →ₙₐ[R] P)
    (hg : ∀ (S T : Finset ι) (h : S ⊆ T) x, g T (stageMap R e h x) = g S x) :
    RestrictedTensorAlgebra R A e he →ₙₐ[R] P :=
  DirectLimit.NonUnitalAlgebra.lift _ _ P g hg

/-- The induced morphism on a finite stage. -/
@[simp]
theorem lift_ofFinite (g : ∀ S : Finset ι, (⨂[R] i : S, A i) →ₙₐ[R] P)
    (hg : ∀ (S T : Finset ι) (h : S ⊆ T) x, g T (stageMap R e h x) = g S x)
    (S : Finset ι) (x : ⨂[R] i : S, A i) : lift he g hg (ofFinite he S x) = g S x :=
  DirectLimit.NonUnitalAlgebra.lift_of _ _ _ _ _

end lift

end RestrictedTensorAlgebra

end TauCeti
