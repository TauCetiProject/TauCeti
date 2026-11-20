/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PiTensorProduct.FiberwiseMul
public import TauCeti.RingTheory.PiTensorProduct.Map

/-!
# The factorwise action of a product of monoids on an indexed tensor product

If for each `i` a monoid `G i` acts on an `R`-algebra `A i` by `R`-algebra endomorphisms, then the
product monoid `∀ i, G i` acts on `⨂[R] i, A i` factorwise, by `g • ⨂ₜ aᵢ = ⨂ₜ (g i • aᵢ)`.
Geometrically, the fibre product of the `Spec (A i)` over `Spec R` carries the product of the
actions. This is the indexed analogue of `Algebra.TensorProduct.prodMulSemiringAction`, and the
action under which a finite tensor product of torsors is a torsor under the product group.

For a map `f : σ → τ` of finite index types and a family of commutative algebras `A` on `τ`,
multiplication along the fibres of `f`, `PiTensorProduct.fiberwiseMul f`, is equivariant along
the restriction `(∀ j, G j) → ∀ i, G (f i)`, `g ↦ g ∘ f`.

## Main definitions

* `PiTensorProduct.piMulSemiringAction`: the factorwise action of `∀ i, G i` on `⨂[R] i, A i`,
  by `R`-algebra endomorphisms.

## Main results

* `PiTensorProduct.piMulSemiringAction_smul_tprod`,
  `PiTensorProduct.piMulSemiringAction_smul_singleAlgHom`: the action on pure tensors and on the
  factor inclusions.
* `PiTensorProduct.fiberwiseMul_piMulSemiringAction_smul`: `fiberwiseMul f` is equivariant along
  `g ↦ g ∘ f`.

## Implementation notes

The action is not a global instance, following `Algebra.TensorProduct.prodMulSemiringAction`: when
`∀ i, G i` also acts on `R`, Mathlib's action of scalars through `R`
(`PiTensorProduct.hasSMul'`) would make the action of `∀ i, G i` on `⨂[R] i, A i` ambiguous.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} (A : ι → Type*) [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)] (G : ι → Type*) [∀ i, Monoid (G i)] [∀ i, MulSemiringAction (G i) (A i)]
  [∀ i, SMulCommClass (G i) R (A i)]

/-- Monoids `G i` acting on `R`-algebras `A i` by `R`-algebra endomorphisms give an action of
`∀ i, G i` on `⨂[R] i, A i` by `R`-algebra endomorphisms: `g • ⨂ₜ aᵢ = ⨂ₜ (g i • aᵢ)`.

This is not a global instance: when `∀ i, G i` also acts on `R`, Mathlib's action of scalars
through `R` would make the action on `⨂[R] i, A i` ambiguous. -/
noncomputable abbrev piMulSemiringAction : MulSemiringAction (∀ i, G i) (⨂[R] i, A i) where
  smul g := mapAlgHom fun i ↦ MulSemiringAction.toAlgHom R (A i) (g i)
  one_smul x := DFunLike.congr_fun ((congrArg mapAlgHom <| funext fun i ↦
    AlgHom.ext (one_smul (G i))).trans (mapAlgHom_id R A)) x
  mul_smul g h x := (DFunLike.congr_fun (congrArg mapAlgHom <| funext fun i ↦
    AlgHom.ext (mul_smul (g i) (h i))) x).trans (mapAlgHom_mapAlgHom _ _ x).symm
  smul_zero _ := map_zero _
  smul_add _ := map_add _
  smul_one _ := map_one _
  smul_mul _ := map_mul _

attribute [local instance] piMulSemiringAction

variable {A G}

/-- The factorwise action of `g : ∀ i, G i` is the `R`-algebra map applying `g i` in slot `i`. -/
theorem piMulSemiringAction_smul_def (g : ∀ i, G i) (x : ⨂[R] i, A i) :
    g • x = mapAlgHom (fun i ↦ MulSemiringAction.toAlgHom R (A i) (g i)) x :=
  (rfl)

/-- The factorwise action on a pure tensor. -/
@[simp]
theorem piMulSemiringAction_smul_tprod (g : ∀ i, G i) (a : ∀ i, A i) :
    g • tprod R a = tprod R fun i ↦ g i • a i := by
  simp [piMulSemiringAction_smul_def]

/-- The factorwise action on the factor inclusion at `i` acts by `g i` in slot `i`. It is a
pre-simp lemma since `singleAlgHom_apply` would otherwise unfold the factor inclusion first. -/
@[simp↓]
theorem piMulSemiringAction_smul_singleAlgHom [DecidableEq ι] (g : ∀ i, G i) (i : ι) (a : A i) :
    g • singleAlgHom (R := R) i a = singleAlgHom i (g i • a) := by
  rw [piMulSemiringAction_smul_def, mapAlgHom_singleAlgHom, MulSemiringAction.toAlgHom_apply]

/-- The factorwise action is by `R`-linear maps. -/
instance piMulSemiringAction_smulCommClass : SMulCommClass (∀ i, G i) R (⨂[R] i, A i) where
  smul_comm g r x := by
    simp only [piMulSemiringAction_smul_def, map_smul]

section FiberwiseMul

variable {σ τ : Type*} [Fintype σ] [DecidableEq τ] {A : τ → Type*}
  [∀ j, CommSemiring (A j)] [∀ j, Algebra R (A j)] {G : τ → Type*} [∀ j, Monoid (G j)]
  [∀ j, MulSemiringAction (G j) (A j)] [∀ j, SMulCommClass (G j) R (A j)]

/-- Multiplication along the fibres of `f : σ → τ` is equivariant along the restriction
`g ↦ g ∘ f` from `∀ j, G j` to `∀ i, G (f i)`. -/
theorem fiberwiseMul_piMulSemiringAction_smul (f : σ → τ) (g : ∀ j, G j)
    (x : ⨂[R] i, A (f i)) :
    fiberwiseMul f ((fun i ↦ g (f i)) • x) = g • fiberwiseMul f x := by
  classical
  -- Both sides are algebra maps in `x`; compare them on the factor inclusions.
  have h := algHom_ext (R := R) (A := fun i ↦ A (f i))
    (f := (fiberwiseMul f).comp
      (mapAlgHom fun i ↦ MulSemiringAction.toAlgHom R (A (f i)) (g (f i))))
    (g := (mapAlgHom fun j ↦ MulSemiringAction.toAlgHom R (A j) (g j)).comp (fiberwiseMul f))
    fun i ↦ AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, mapAlgHom_singleAlgHom, fiberwiseMul_singleAlgHom]
  rw [piMulSemiringAction_smul_def, piMulSemiringAction_smul_def]
  exact DFunLike.congr_fun h x

end FiberwiseMul

end PiTensorProduct
