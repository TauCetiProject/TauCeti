/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
public import TauCeti.RingTheory.PiTensorProduct.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# The tensor-induced algebra and its twisted multiplication

Let `D` be a group acting on an `R`-algebra `A` by `R`-algebra automorphisms, and let `ι` be an
index type. The permutation wreath product `(ι → D) ⋊ Equiv.Perm ι` acts on the indexed tensor
power `⨂[R] _ : ι, A` by `R`-algebra automorphisms: the top permutation reindexes the tensor
factors through `PiTensorProduct.permAlgEquiv`, and the base coordinates act slotwise through
`PiTensorProduct.congrAlgEquiv`. On underlying `R`-modules this action is
`Representation.wreathTensor`.

Pulling back along the monomial embedding `Subgroup.monomialHom` attached to a left transversal `s`
of a subgroup `U ≤ G` makes the coset-indexed tensor power `⨂[R] _ : G ⧸ U, A` an `R`-algebra with
`G`-action (`Subgroup.tensorInducedAlgAut`), whose underlying `G`-representation is
`Subgroup.tensorInducedRepresentation` (and, over a commutative ring, the object map of
`Subgroup.tensorInductionFunctor`). Changing the transversal conjugates the monomial embedding by
`Subgroup.monomialChangeTransversal`, yielding an `R`-algebra isomorphism
`Subgroup.tensorInducedChangeTransversalAlgEquiv` that intertwines the two `G`-actions. Neither the
action nor the change-of-transversal algebra isomorphism requires `A` to be commutative, `G ⧸ U` to
be finite, or the `U`-action on `A` to extend to `G`.

When `A` is a commutative `G`-algebra over `R` and `G ⧸ U` is finite, Evens's twisted
multiplication (`Subgroup.tensorInducedMulAlgHom`) is the `R`-algebra homomorphism
`⨂[R] _ : G ⧸ U, A →ₐ[R] A` determined on pure tensors by
```text
⨂ₜ x, a x ↦ ∏ x : G ⧸ U, r_s(x) • a x,
```
where `r_s : G ⧸ U → G` picks the representatives of `s`. Bundling it as an `R`-algebra
homomorphism records preservation of `1`, products, sums, and scalars directly in its type. Using
the rewriting rule `r_s(x) * ℓ^s_x(g) = g * r_s(g⁻¹ • x)` (`TauCeti.transversal_mul_lWord`), the
twisted multiplication is `G`-equivariant (`Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut`),
and using `r_s(x) * d^{s,t}_x = r_t(x)` (`TauCeti.transversal_mul_transversalDiff`), it commutes
with `Subgroup.tensorInducedChangeTransversalAlgEquiv`. When `G` acts trivially on `A` it reduces
to `PiTensorProduct.mulAlgHom`, and when `G ⧸ U` is a subsingleton with representative `1` it
reduces to `PiTensorProduct.subsingletonAlgEquiv`.

## Main definitions

* `TauCeti.WreathProduct.tensorAlgAut`: the homomorphism from `WreathProduct D ι` to the group of
  `R`-algebra automorphisms of `⨂[R] _ : ι, A`, equipping the tensor power with a
  `MulSemiringAction`.
* `Subgroup.tensorInducedAlgAut`: the tensor-induced `G`-action on `⨂[R] _ : G ⧸ U, A` by
  `R`-algebra automorphisms, with `Subgroup.tensorInducedMulSemiringAction` as its named
  `MulSemiringAction`.
* `Subgroup.tensorInducedChangeTransversalAlgEquiv`: the `R`-algebra isomorphism comparing tensor
  induction along two left transversals.
* `Subgroup.tensorInducedMulAlgHom`: Evens's twisted multiplication `(⨂[R] _ : G ⧸ U, A) →ₐ[R] A`
  along a left transversal, with `Subgroup.tensorInducedMulIntertwiningMap` and
  `Subgroup.tensorInducedMulRepHom` as its bundled representation morphisms.

## Main results

* `Subgroup.tensorInducedAlgAut_toLinearMap`,
  `Subgroup.tensorInductionFunctor_obj_ofDistribMulAction`: the tensor-induced algebra action
  agrees with `Subgroup.tensorInducedRepresentation` and `Subgroup.tensorInductionFunctor`.
* `Subgroup.tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut`: the change-of-transversal
  algebra isomorphism intertwines the tensor-induced `G`-actions.
* `Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut`: Evens's twisted multiplication is
  `G`-equivariant.
* `Subgroup.tensorInducedMulAlgHom_changeTransversalAlgEquiv`: Evens's twisted multiplication is
  independent of the chosen transversal up to `Subgroup.tensorInducedChangeTransversalAlgEquiv`.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5, especially §5, p. 60.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

namespace TauCeti.WreathProduct

section Semiring

variable (R : Type u) (D : Type v) (A : Type w) (ι : Type x)
  [CommSemiring R] [Group D] [Semiring A] [Algebra R A]
  [MulSemiringAction D A] [SMulCommClass D R A]

/-- The permutation wreath product `(ι → D) ⋊ Equiv.Perm ι` acts on the indexed tensor power
`⨂[R] _ : ι, A` by `R`-algebra automorphisms: the top permutation reindexes the tensor factors and
the base coordinates act independently in each factor. -/
noncomputable def tensorAlgAut :
    WreathProduct D ι →* ((⨂[R] _ : ι, A) ≃ₐ[R] ⨂[R] _ : ι, A) where
  toFun w :=
    PiTensorProduct.congrAlgEquiv (fun i ↦ MulSemiringAction.toAlgAut D R A (w.left i)) *
      PiTensorProduct.permAlgEquiv A w.right
  map_one' := AlgEquiv.ext fun z ↦ by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r a => simp [Equiv.Perm.one_def]
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
  map_mul' w₁ w₂ := AlgEquiv.ext fun z ↦ by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      simp [PermutationWreathProduct.mul_left, mul_smul, Equiv.Perm.mul_def]
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]

variable {R D A ι}

/-- The wreath-product algebra automorphism factors as factorwise reindexing followed by the
coordinatewise algebra automorphisms of the base group. -/
theorem tensorAlgAut_apply (w : WreathProduct D ι) :
    tensorAlgAut R D A ι w =
      PiTensorProduct.congrAlgEquiv (fun i ↦ MulSemiringAction.toAlgAut D R A (w.left i)) *
        PiTensorProduct.permAlgEquiv A w.right := (rfl)

/-- On a pure tensor, `TauCeti.WreathProduct.tensorAlgAut` reindexes the factors by the inverse of
the top permutation and acts in slot `i` by the `i`-th coordinate of the base element. -/
@[simp]
theorem tensorAlgAut_tprod (w : WreathProduct D ι) (a : ι → A) :
    tensorAlgAut R D A ι w (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R fun i ↦ w.left i • a (w.right.symm i) := by
  simp [tensorAlgAut_apply, Function.comp_def]

/-- The base subgroup of the wreath product acts factorwise on pure tensors.

This is an explicit rewrite rule rather than a `simp` lemma because `tensorAlgAut_tprod` already
simplifies its left-hand side. -/
theorem tensorAlgAut_inl_tprod (d : ι → D) (a : ι → A) :
    tensorAlgAut R D A ι (SemidirectProduct.inl d) (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R fun i ↦ d i • a i := by
  rw [tensorAlgAut_tprod]
  congr 1

/-- The top symmetric subgroup of the wreath product acts by permuting pure-tensor factors.

This is an explicit rewrite rule rather than a `simp` lemma because `tensorAlgAut_tprod` already
simplifies its left-hand side. -/
theorem tensorAlgAut_inr_tprod (σ : Equiv.Perm ι) (a : ι → A) :
    tensorAlgAut R D A ι (SemidirectProduct.inr σ) (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R fun i ↦ a (σ.symm i) := by
  simp

/-- `TauCeti.WreathProduct.tensorAlgAut` carries `a` in slot `i` to `w.left (w.right i) • a` in
slot `w.right i`. It is a pre-simp lemma since `PiTensorProduct.singleAlgHom_apply` would otherwise
expand the factor inclusion first. -/
@[simp↓]
theorem tensorAlgAut_singleAlgHom [DecidableEq ι] (w : WreathProduct D ι) (i : ι) (a : A) :
    tensorAlgAut R D A ι w (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom (w.right i) (w.left (w.right i) • a) := by
  rw [tensorAlgAut_apply, AlgEquiv.mul_apply, PiTensorProduct.permAlgEquiv_singleAlgHom,
    PiTensorProduct.congrAlgEquiv_singleAlgHom, MulSemiringAction.toAlgAut_apply,
    MulSemiringAction.toAlgEquiv_apply]

/-- Forgetting the multiplicative structure recovers `Representation.wreathTensor` of the
underlying `D`-representation on `A`. -/
@[simp]
theorem tensorAlgAut_toLinearMap (w : WreathProduct D ι) :
    (tensorAlgAut R D A ι w).toLinearMap =
      (Representation.ofDistribMulAction R D A).wreathTensor ι w := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun a ↦ ?_)
  simp

/-- Postcomposing `TauCeti.WreathProduct.tensorAlgAut` with `AlgEquiv.toLinearMapHom` recovers the
representation `Representation.wreathTensor`. -/
theorem toLinearMapHom_comp_tensorAlgAut :
    (AlgEquiv.toLinearMapHom R (⨂[R] _ : ι, A)).comp (tensorAlgAut R D A ι) =
      (Representation.ofDistribMulAction R D A).wreathTensor ι :=
  MonoidHom.ext tensorAlgAut_toLinearMap

/-- The canonical action of `WreathProduct D ι` on `⨂[R] _ : ι, A` by semiring automorphisms. -/
noncomputable instance instMulSemiringActionPiTensorProduct :
    MulSemiringAction (WreathProduct D ι) (⨂[R] _ : ι, A) :=
  MulSemiringAction.compHom _ (tensorAlgAut R D A ι)

/-- The wreath-product action on `⨂[R] _ : ι, A` commutes with scalars from `R`. -/
instance instSMulCommClassPiTensorProduct :
    SMulCommClass (WreathProduct D ι) R (⨂[R] _ : ι, A) where
  smul_comm w r z := map_smul (tensorAlgAut R D A ι w) r z

/-- Scalar multiplication by `w : WreathProduct D ι` on `⨂[R] _ : ι, A` is evaluation of
`TauCeti.WreathProduct.tensorAlgAut`. -/
theorem smul_piTensorProduct_def (w : WreathProduct D ι) (z : ⨂[R] _ : ι, A) :
    w • z = tensorAlgAut R D A ι w z := (rfl)

/-- Scalar multiplication by `w : WreathProduct D ι` on a pure tensor reindexes by `w.right⁻¹` and
acts coordinatewise by `w.left`. -/
@[simp]
theorem smul_tprod (w : WreathProduct D ι) (a : ι → A) :
    w • PiTensorProduct.tprod R a =
      PiTensorProduct.tprod R fun i ↦ w.left i • a (w.right.symm i) :=
  tensorAlgAut_tprod w a

/-- Scalar multiplication by `w : WreathProduct D ι` moves the factor inclusion at `i` to slot
`w.right i` and acts on its entry by `w.left (w.right i)`. -/
@[simp↓]
theorem smul_singleAlgHom [DecidableEq ι] (w : WreathProduct D ι) (i : ι) (a : A) :
    w • PiTensorProduct.singleAlgHom (R := R) (A := fun _ ↦ A) i a =
      PiTensorProduct.singleAlgHom (w.right i) (w.left (w.right i) • a) :=
  tensorAlgAut_singleAlgHom w i a

end Semiring

end TauCeti.WreathProduct

namespace Subgroup

open TauCeti

/-! ### The tensor-induced algebra and change of transversal -/

section TensorInducedAlgebra

variable {G : Type v} [Group G] (U : Subgroup G)
  (R : Type u) [CommSemiring R] (A : Type w) [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

/-- **The tensor-induced algebra action**: pulling `TauCeti.WreathProduct.tensorAlgAut` back along
the monomial homomorphism of a left transversal `s : U.LeftTransversal` makes `G` act on the
coset-indexed tensor power `⨂[R] _ : G ⧸ U, A` by `R`-algebra automorphisms. -/
noncomputable def tensorInducedAlgAut (s : U.LeftTransversal) :
    G →* ((⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A) :=
  (WreathProduct.tensorAlgAut R U A (G ⧸ U)).comp (U.monomialHom s)

/-- The tensor-induced algebra automorphism of `g` is the wreath-product algebra automorphism of
`U.monomialHom s g`. -/
theorem tensorInducedAlgAut_apply (s : U.LeftTransversal) (g : G) :
    U.tensorInducedAlgAut R A s g =
      WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialHom s g) := (rfl)

/-- On a pure tensor, `Subgroup.tensorInducedAlgAut` translates the coset coordinates by `g⁻¹` and
acts in slot `x` by the Schreier factor `(U.monomialHom s g).left x`. -/
@[simp]
theorem tensorInducedAlgAut_tprod (s : U.LeftTransversal) (g : G) (a : G ⧸ U → A) :
    U.tensorInducedAlgAut R A s g (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialHom s g).left x • a (g⁻¹ • x) := by
  rw [tensorInducedAlgAut_apply, WreathProduct.tensorAlgAut_tprod]
  congr 1
  funext x
  rw [← Equiv.Perm.coe_inv, U.monomialHom_right_inv]

/-- `Subgroup.tensorInducedAlgAut` sends `a` in coset slot `x` to
`(U.monomialHom s g).left (g • x) • a` in slot `g • x`. It is a pre-simp lemma since
`PiTensorProduct.singleAlgHom_apply` would otherwise expand the factor inclusion first. -/
@[simp↓]
theorem tensorInducedAlgAut_singleAlgHom [DecidableEq (G ⧸ U)] (s : U.LeftTransversal)
    (g : G) (x : G ⧸ U) (a : A) :
    U.tensorInducedAlgAut R A s g (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom (g • x) ((U.monomialHom s g).left (g • x) • a) := by
  rw [tensorInducedAlgAut_apply, WreathProduct.tensorAlgAut_singleAlgHom, U.monomialHom_right]

/-- The linear map underlying `Subgroup.tensorInducedAlgAut` is
`Subgroup.tensorInducedRepresentation` applied to `Representation.ofDistribMulAction R U A`. -/
@[simp]
theorem tensorInducedAlgAut_toLinearMap (s : U.LeftTransversal) (g : G) :
    (U.tensorInducedAlgAut R A s g).toLinearMap =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g := by
  apply LinearMap.ext
  intro z
  rw [tensorInducedAlgAut_apply, U.tensorInducedRepresentation_apply,
    ← WreathProduct.tensorAlgAut_toLinearMap]

/-- Forgetting the multiplicative structure of `Subgroup.tensorInducedAlgAut` recovers
`Subgroup.tensorInducedRepresentation`. -/
theorem toLinearMapHom_comp_tensorInducedAlgAut (s : U.LeftTransversal) :
    (AlgEquiv.toLinearMapHom R (⨂[R] _ : G ⧸ U, A)).comp (U.tensorInducedAlgAut R A s) =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) :=
  MonoidHom.ext (U.tensorInducedAlgAut_toLinearMap R A s)

/-- The `MulSemiringAction` of `G` on `⨂[R] _ : G ⧸ U, A` induced by a left transversal `s`.

This is a definition rather than a global instance because the action depends on the chosen left
transversal `s : U.LeftTransversal`. -/
@[instance_reducible]
noncomputable def tensorInducedMulSemiringAction (s : U.LeftTransversal) :
    MulSemiringAction G (⨂[R] _ : G ⧸ U, A) :=
  MulSemiringAction.compHom _ (U.tensorInducedAlgAut R A s)

/-- In `Subgroup.tensorInducedMulSemiringAction`, `g` acts by `Subgroup.tensorInducedAlgAut`. -/
@[simp]
theorem tensorInducedMulSemiringAction_smul (s : U.LeftTransversal) (g : G)
    (z : ⨂[R] _ : G ⧸ U, A) :
    letI := U.tensorInducedMulSemiringAction R A s
    g • z = U.tensorInducedAlgAut R A s g z := (rfl)

/-- Scalar multiplication in `Subgroup.tensorInducedMulSemiringAction` commutes with `R`. -/
theorem tensorInducedSMulCommClass (s : U.LeftTransversal) :
    @SMulCommClass G R (⨂[R] _ : G ⧸ U, A) (U.tensorInducedMulSemiringAction R A s).toSMul _ :=
  let := U.tensorInducedMulSemiringAction R A s
  ⟨fun g r z ↦ map_smul (U.tensorInducedAlgAut R A s g) r z⟩

/-- **Change-of-transversal algebra isomorphism**: comparing two left transversals `s` and `t`
through `Subgroup.monomialChangeTransversal` gives an `R`-algebra automorphism of
`⨂[R] _ : G ⧸ U, A` that intertwines the `t`-action with the `s`-action. -/
noncomputable def tensorInducedChangeTransversalAlgEquiv (s t : U.LeftTransversal) :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A :=
  WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialChangeTransversal s t)

/-- The change-of-transversal algebra equivalence is the wreath-product algebra automorphism of
`Subgroup.monomialChangeTransversal`. -/
theorem tensorInducedChangeTransversalAlgEquiv_def (s t : U.LeftTransversal) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t =
      WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialChangeTransversal s t) := (rfl)

/-- Forgetting the algebra structure of `Subgroup.tensorInducedChangeTransversalAlgEquiv` recovers
`Subgroup.tensorInducedChangeTransversalLinearEquiv`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_toLinearEquiv (s t : U.LeftTransversal) :
    (U.tensorInducedChangeTransversalAlgEquiv R A s t).toLinearEquiv =
      U.tensorInducedChangeTransversalLinearEquiv s t
        (Representation.ofDistribMulAction R U A) := by
  apply LinearEquiv.ext
  intro z
  rw [U.tensorInducedChangeTransversalLinearEquiv_apply, ← WreathProduct.tensorAlgAut_toLinearMap]
  rfl

/-- On a pure tensor, `Subgroup.tensorInducedChangeTransversalAlgEquiv` acts in each coset factor
by the transversal difference `(U.monomialChangeTransversal s t).left x`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_tprod (s t : U.LeftTransversal) (a : G ⧸ U → A) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t (PiTensorProduct.tprod R a) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialChangeTransversal s t).left x • a x := by
  rw [tensorInducedChangeTransversalAlgEquiv_def, WreathProduct.tensorAlgAut_tprod]
  simp only [monomialChangeTransversal_right, ← Equiv.Perm.inv_def, inv_one, Equiv.Perm.coe_one,
    id_eq]

/-- On a factor inclusion at `x`, `Subgroup.tensorInducedChangeTransversalAlgEquiv` acts on the
entry in slot `x` by `(U.monomialChangeTransversal s t).left x`. -/
@[simp↓]
theorem tensorInducedChangeTransversalAlgEquiv_singleAlgHom [DecidableEq (G ⧸ U)]
    (s t : U.LeftTransversal) (x : G ⧸ U) (a : A) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom x ((U.monomialChangeTransversal s t).left x • a) := by
  rw [tensorInducedChangeTransversalAlgEquiv_def, WreathProduct.tensorAlgAut_singleAlgHom,
    monomialChangeTransversal_right, Equiv.Perm.coe_one, id_eq]

/-- Comparing a transversal with itself gives the identity algebra equivalence. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_self (s : U.LeftTransversal) :
    U.tensorInducedChangeTransversalAlgEquiv R A s s = AlgEquiv.refl := by
  rw [tensorInducedChangeTransversalAlgEquiv_def, monomialChangeTransversal_self, map_one,
    AlgEquiv.aut_one]

/-- Change-of-transversal algebra equivalences compose across an intermediate transversal. -/
theorem tensorInducedChangeTransversalAlgEquiv_trans (s t v : U.LeftTransversal) :
    (U.tensorInducedChangeTransversalAlgEquiv R A t v).trans
        (U.tensorInducedChangeTransversalAlgEquiv R A s t) =
      U.tensorInducedChangeTransversalAlgEquiv R A s v := by
  rw [← AlgEquiv.aut_mul, tensorInducedChangeTransversalAlgEquiv_def,
    tensorInducedChangeTransversalAlgEquiv_def, tensorInducedChangeTransversalAlgEquiv_def,
    ← map_mul, monomialChangeTransversal_mul]

/-- Swapping the two transversals gives the inverse algebra equivalence. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_symm (s t : U.LeftTransversal) :
    (U.tensorInducedChangeTransversalAlgEquiv R A s t).symm =
      U.tensorInducedChangeTransversalAlgEquiv R A t s := by
  apply AlgEquiv.ext
  intro z
  apply (U.tensorInducedChangeTransversalAlgEquiv R A s t).injective
  rw [AlgEquiv.apply_symm_apply]
  have h := AlgEquiv.congr_fun (U.tensorInducedChangeTransversalAlgEquiv_trans R A s t s) z
  simpa using h.symm

/-- In the algebra automorphism group of `⨂[R] _ : G ⧸ U, A`, the change-of-transversal element
intertwines the `t`-action with the `s`-action. -/
theorem tensorInducedChangeTransversalAlgEquiv_mul_tensorInducedAlgAut
    (s t : U.LeftTransversal) (g : G) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t * U.tensorInducedAlgAut R A t g =
      U.tensorInducedAlgAut R A s g * U.tensorInducedChangeTransversalAlgEquiv R A s t := by
  rw [tensorInducedChangeTransversalAlgEquiv_def, tensorInducedAlgAut_apply,
    tensorInducedAlgAut_apply, ← map_mul, ← map_mul, monomialChangeTransversal_mul_monomialHom]

/-- Pointwise `G`-equivariance of `Subgroup.tensorInducedChangeTransversalAlgEquiv`: it carries the
tensor-induced `G`-action for `t` to the tensor-induced `G`-action for `s`. -/
theorem tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut
    (s t : U.LeftTransversal) (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t (U.tensorInducedAlgAut R A t g z) =
      U.tensorInducedAlgAut R A s g (U.tensorInducedChangeTransversalAlgEquiv R A s t z) :=
  AlgEquiv.congr_fun (U.tensorInducedChangeTransversalAlgEquiv_mul_tensorInducedAlgAut R A s t g) z

/-- Over a single coset `x₀`, `Subgroup.tensorInducedAlgAut` acts through
`PiTensorProduct.subsingletonAlgEquiv` by `(U.monomialHom s g).left x₀`. -/
theorem subsingletonAlgEquiv_tensorInducedAlgAut [Subsingleton (G ⧸ U)] (x₀ : G ⧸ U)
    (s : U.LeftTransversal) (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ ↦ A) (U.tensorInducedAlgAut R A s g z) =
      (U.monomialHom s g).left x₀ • PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ ↦ A) z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    simp only [map_smul, tensorInducedAlgAut_tprod, PiTensorProduct.subsingletonAlgEquiv_tprod,
      smul_comm ((U.monomialHom s g).left x₀) r]
    rw [Subsingleton.elim (g⁻¹ • x₀) x₀]
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, smul_add, hz₁, hz₂]

end TensorInducedAlgebra

section TensorInductionFunctor

variable {G : Type v} [Group G] (U : Subgroup G)
  (R : Type u) [CommRing R] (A : Type w) [Ring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

/-- On the bundled `U`-representation `Rep.of (Representation.ofDistribMulAction R U A)`,
`Subgroup.tensorInductionFunctor` produces the representation underlying
`Subgroup.tensorInducedAlgAut`. -/
theorem tensorInductionFunctor_obj_ofDistribMulAction (s : U.LeftTransversal) :
    (U.tensorInductionFunctor (R := R) s).obj (Rep.of (Representation.ofDistribMulAction R U A)) =
      Rep.of ((AlgEquiv.toLinearMapHom R (⨂[R] _ : G ⧸ U, A)).comp
        (U.tensorInducedAlgAut R A s)) := by
  rw [U.tensorInductionFunctor_obj, Rep.of_ρ, U.toLinearMapHom_comp_tensorInducedAlgAut]

end TensorInductionFunctor

/-! ### Evens's twisted multiplication along a transversal -/

section TwistedMultiplication

variable {G : Type v} [Group G] (U : Subgroup G)
  (R : Type u) [CommSemiring R] (A : Type w) [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- **Evens's twisted multiplication** (Evens 1963, §5, p. 60): for a commutative `G`-algebra `A`
over `R` and a finite-index subgroup `U ≤ G` with left transversal `s`, the `R`-algebra
homomorphism `(⨂[R] _ : G ⧸ U, A) →ₐ[R] A` sending a pure tensor `⨂ₜ x, a x` to
`∏ x : G ⧸ U, r_s(x) • a x`. -/
noncomputable def tensorInducedMulAlgHom (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (⨂[R] _ : G ⧸ U, A) →ₐ[R] A :=
  PiTensorProduct.productMap fun x ↦ MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x)

/-- `Subgroup.tensorInducedMulAlgHom` is the coproduct `PiTensorProduct.productMap` of the
transversal-representative algebra actions. -/
theorem tensorInducedMulAlgHom_def (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    U.tensorInducedMulAlgHom R A s =
      PiTensorProduct.productMap fun x ↦
        MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x) := (rfl)

/-- On a pure tensor, `Subgroup.tensorInducedMulAlgHom` multiplies the factors after acting on the
`x`-th factor by the chosen representative `U.leftTransversalRep s x`. -/
@[simp]
theorem tensorInducedMulAlgHom_tprod (s : U.LeftTransversal) [Fintype (G ⧸ U)] (a : G ⧸ U → A) :
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R a) =
      ∏ x, U.leftTransversalRep s x • a x := by
  simp only [tensorInducedMulAlgHom_def, PiTensorProduct.productMap_tprod,
    MulSemiringAction.toAlgHom_apply]

/-- On the factor inclusion at a coset `x`, `Subgroup.tensorInducedMulAlgHom` acts by the chosen
coset representative `U.leftTransversalRep s x`. It is a pre-simp lemma since
`PiTensorProduct.singleAlgHom_apply` would otherwise expand the factor inclusion first. -/
@[simp↓]
theorem tensorInducedMulAlgHom_singleAlgHom (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.singleAlgHom x a) =
      U.leftTransversalRep s x • a := by
  rw [tensorInducedMulAlgHom_def, PiTensorProduct.productMap_singleAlgHom,
    MulSemiringAction.toAlgHom_apply]

/-- Restricting `Subgroup.tensorInducedMulAlgHom` along the factor inclusion at `x` recovers the
algebra endomorphism of `U.leftTransversalRep s x`. -/
@[simp]
theorem tensorInducedMulAlgHom_comp_singleAlgHom (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    [DecidableEq (G ⧸ U)] (x : G ⧸ U) :
    (U.tensorInducedMulAlgHom R A s).comp (PiTensorProduct.singleAlgHom x) =
      MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x) :=
  AlgHom.ext (U.tensorInducedMulAlgHom_singleAlgHom R A s x)

/-- `Subgroup.tensorInducedMulAlgHom` is independent of the `Fintype (G ⧸ U)` instance. -/
theorem tensorInducedMulAlgHom_congr_fintype (s : U.LeftTransversal)
    (inst₁ inst₂ : Fintype (G ⧸ U)) :
    @tensorInducedMulAlgHom G _ U R _ A _ _ _ _ s inst₁ =
      @tensorInducedMulAlgHom G _ U R _ A _ _ _ _ s inst₂ := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- **`G`-equivariance of Evens's twisted multiplication**: `Subgroup.tensorInducedMulAlgHom`
intertwines the tensor-induced `G`-action on `⨂[R] _ : G ⧸ U, A` with the `G`-action on `A`. -/
@[simp]
theorem tensorInducedMulAlgHom_tensorInducedAlgAut (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom R A s (U.tensorInducedAlgAut R A s g z) =
      g • U.tensorInducedMulAlgHom R A s z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [map_smul, map_smul, map_smul, smul_comm g r, tensorInducedAlgAut_tprod,
      tensorInducedMulAlgHom_tprod, tensorInducedMulAlgHom_tprod]
    congr 1
    calc
      ∏ x, U.leftTransversalRep s x • ((U.monomialHom s g).left x • a (g⁻¹ • x))
        = ∏ x, (U.leftTransversalRep s x * lWord U (U.leftTransversalRep s) x g) •
            a (g⁻¹ • x) := by
          refine Finset.prod_congr rfl fun x _ ↦ ?_
          rw [Subgroup.monomialHom_left, Subgroup.smul_def, Subtype.coe_mk, mul_smul]
      _ = ∏ x, g • (U.leftTransversalRep s (g⁻¹ • x) • a (g⁻¹ • x)) := by
          refine Finset.prod_congr rfl fun x _ ↦ ?_
          rw [transversal_mul_lWord, mul_smul]
      _ = g • ∏ x, U.leftTransversalRep s (g⁻¹ • x) • a (g⁻¹ • x) :=
          (map_prod (MulSemiringAction.toRingHom G A g) _ _).symm
      _ = g • ∏ x, U.leftTransversalRep s x • a x := by
          congr 1
          exact Equiv.prod_comp (MulAction.toPerm g⁻¹) fun x ↦ U.leftTransversalRep s x • a x
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, map_add, map_add, smul_add, hz₁, hz₂]

/-- `G`-equivariance of `Subgroup.tensorInducedMulAlgHom` stated as an equality of `R`-algebra
homomorphisms. -/
theorem tensorInducedMulAlgHom_comp_tensorInducedAlgAut (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (g : G) :
    (U.tensorInducedMulAlgHom R A s).comp (U.tensorInducedAlgAut R A s g).toAlgHom =
      (MulSemiringAction.toAlgHom R A g).comp (U.tensorInducedMulAlgHom R A s) :=
  AlgHom.ext (U.tensorInducedMulAlgHom_tensorInducedAlgAut R A s g)

/-- **Independence of the transversal**: composing `Subgroup.tensorInducedMulAlgHom` for `s` with
`Subgroup.tensorInducedChangeTransversalAlgEquiv` from `t` to `s` recovers
`Subgroup.tensorInducedMulAlgHom` for `t`. -/
@[simp]
theorem tensorInducedMulAlgHom_changeTransversalAlgEquiv (s t : U.LeftTransversal)
    [Fintype (G ⧸ U)] (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom R A s (U.tensorInducedChangeTransversalAlgEquiv R A s t z) =
      U.tensorInducedMulAlgHom R A t z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [map_smul, map_smul, map_smul, tensorInducedChangeTransversalAlgEquiv_tprod,
      tensorInducedMulAlgHom_tprod, tensorInducedMulAlgHom_tprod]
    congr 1
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [monomialChangeTransversal_left, Subgroup.smul_def, Subtype.coe_mk, ← mul_smul,
      transversal_mul_transversalDiff]
  | add z₁ z₂ hz₁ hz₂ =>
    rw [map_add, map_add, map_add, hz₁, hz₂]

/-- Independence of the transversal as an equality of `R`-algebra homomorphisms. -/
@[simp]
theorem tensorInducedMulAlgHom_comp_changeTransversalAlgEquiv (s t : U.LeftTransversal)
    [Fintype (G ⧸ U)] :
    (U.tensorInducedMulAlgHom R A s).comp
        (U.tensorInducedChangeTransversalAlgEquiv R A s t).toAlgHom =
      U.tensorInducedMulAlgHom R A t :=
  AlgHom.ext (U.tensorInducedMulAlgHom_changeTransversalAlgEquiv R A s t)

/-- Evens's twisted multiplication bundled as a `G`-intertwining `R`-linear map from
`Subgroup.tensorInducedRepresentation` to `A`. -/
noncomputable def tensorInducedMulIntertwiningMap (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedRepresentation s
      (Representation.ofDistribMulAction R U A)).IntertwiningMap
      (Representation.ofDistribMulAction R G A) where
  toLinearMap := (U.tensorInducedMulAlgHom R A s).toLinearMap
  isIntertwining' g := LinearMap.ext fun z ↦ by
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ← U.tensorInducedAlgAut_toLinearMap R A s g,
      AlgEquiv.toLinearMap_apply, Representation.ofDistribMulAction_apply_apply] using
      U.tensorInducedMulAlgHom_tensorInducedAlgAut R A s g z

/-- The linear map underlying `Subgroup.tensorInducedMulIntertwiningMap` is
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_toLinearMap (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedMulIntertwiningMap R A s).toLinearMap =
      (U.tensorInducedMulAlgHom R A s).toLinearMap := (rfl)

/-- Evaluating `Subgroup.tensorInducedMulIntertwiningMap` evaluates
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_apply (s : U.LeftTransversal) [Fintype (G ⧸ U)]
    (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulIntertwiningMap R A s z = U.tensorInducedMulAlgHom R A s z := (rfl)

/-- `Subgroup.tensorInducedMulIntertwiningMap` commutes with
`Subgroup.tensorInducedChangeTransversal`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_comp_changeTransversal
    (s t : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedMulIntertwiningMap R A s).comp
        (U.tensorInducedChangeTransversal s t
          (Representation.ofDistribMulAction R U A)).toIntertwiningMap =
      U.tensorInducedMulIntertwiningMap R A t := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  simpa only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    tensorInducedMulIntertwiningMap_toLinearMap, AlgHom.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.Equiv.coe_toIntertwiningMap,
    U.tensorInducedChangeTransversal_apply,
    ← U.tensorInducedChangeTransversalAlgEquiv_toLinearEquiv R A s t,
    AlgEquiv.coe_toLinearEquiv] using
    U.tensorInducedMulAlgHom_changeTransversalAlgEquiv R A s t z

/-! ### Specializations: trivial action and single coset -/

/-- When `G` acts trivially on `A`, Evens's twisted multiplication reduces to untwisted
multiplication `PiTensorProduct.mulAlgHom` of the tensor factors. -/
theorem tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] (hA : ∀ (g : G) (a : A), g • a = a) :
    U.tensorInducedMulAlgHom R A s = PiTensorProduct.mulAlgHom := by
  classical
  refine PiTensorProduct.algHom_ext fun x ↦ AlgHom.ext fun a ↦ ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, tensorInducedMulAlgHom_singleAlgHom,
    PiTensorProduct.mulAlgHom_singleAlgHom, hA]

/-- Over a single coset `x₀`, composing `Subgroup.tensorInducedMulAlgHom` with the inverse of
`PiTensorProduct.subsingletonAlgEquiv` is the algebra action of `U.leftTransversalRep s x₀`. -/
@[simp]
theorem tensorInducedMulAlgHom_comp_subsingletonAlgEquiv_symm (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] [Subsingleton (G ⧸ U)] (x₀ : G ⧸ U) :
    (U.tensorInducedMulAlgHom R A s).comp
        (PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ : G ⧸ U ↦ A)).symm.toAlgHom =
      MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x₀) := by
  refine AlgHom.ext fun a ↦ ?_
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, PiTensorProduct.subsingletonAlgEquiv_symm_apply',
    tensorInducedMulAlgHom_tprod, MulSemiringAction.toAlgHom_apply]
  exact Finset.prod_eq_single x₀ (fun x _ hx ↦ absurd (Subsingleton.elim x x₀) hx)
    fun hx₀ ↦ absurd (Finset.mem_univ x₀) hx₀

/-- Over a single coset `x₀`, `Subgroup.tensorInducedMulAlgHom` reads the tensor through
`PiTensorProduct.subsingletonAlgEquiv` and acts by `U.leftTransversalRep s x₀`. -/
theorem tensorInducedMulAlgHom_subsingleton_apply (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] [Subsingleton (G ⧸ U)] (x₀ : G ⧸ U) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom R A s z =
      U.leftTransversalRep s x₀ • PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ ↦ A) z := by
  have h := AlgHom.congr_fun (U.tensorInducedMulAlgHom_comp_subsingletonAlgEquiv_symm R A s x₀)
    (PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ ↦ A) z)
  rwa [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    MulSemiringAction.toAlgHom_apply] at h

/-- Over a single coset `x₀` whose chosen representative is `1`,
`Subgroup.tensorInducedMulAlgHom` is `PiTensorProduct.subsingletonAlgEquiv`. -/
theorem tensorInducedMulAlgHom_eq_subsingletonAlgEquiv_of_rep_eq_one (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] [Subsingleton (G ⧸ U)] (x₀ : G ⧸ U)
    (hs : U.leftTransversalRep s x₀ = 1) :
    U.tensorInducedMulAlgHom R A s =
      (PiTensorProduct.subsingletonAlgEquiv x₀ (fun _ : G ⧸ U ↦ A)).toAlgHom := by
  refine AlgHom.ext fun z ↦ ?_
  rw [U.tensorInducedMulAlgHom_subsingleton_apply R A s x₀ z, hs, one_smul, AlgEquiv.coe_toAlgHom]

end TwistedMultiplication

section TwistedMultiplicationRep

variable {G : Type v} [Group G] (U : Subgroup G)
  (R : Type u) [CommRing R] (A : Type (max u v w)) [CommRing A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- Over a commutative ring, Evens's twisted multiplication bundled as a morphism in
`Rep.{max u v w} R G` from the tensor-induced representation of `A` to `A`.

The source is written in the simp-normal form produced by `Subgroup.tensorInductionFunctor_obj` and
`Rep.of_ρ`, so that projection and composition lemmas below can be `@[simp]`. -/
noncomputable def tensorInducedMulRepHom (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    Rep.of (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)) ⟶
      Rep.of (Representation.ofDistribMulAction R G A) :=
  Rep.ofHom (U.tensorInducedMulIntertwiningMap R A s)

/-- The intertwining map underlying `Subgroup.tensorInducedMulRepHom` is
`Subgroup.tensorInducedMulIntertwiningMap`. -/
@[simp]
theorem tensorInducedMulRepHom_hom (s : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (U.tensorInducedMulRepHom R A s).hom = U.tensorInducedMulIntertwiningMap R A s :=
  Rep.hom_ofHom _

/-- `Subgroup.tensorInducedMulRepHom` commutes with `Subgroup.tensorInducedChangeTransversal`
bundled via `Rep.ofHom` (the simp-normal form of `(Rep.mkIso ...).hom`). -/
@[reassoc (attr := simp)]
theorem ofHom_tensorInducedChangeTransversal_tensorInducedMulRepHom
    (s t : U.LeftTransversal) [Fintype (G ⧸ U)] :
    Rep.ofHom (U.tensorInducedChangeTransversal s t
        (Representation.ofDistribMulAction R U A)).toIntertwiningMap ≫
      U.tensorInducedMulRepHom R A s =
      U.tensorInducedMulRepHom R A t := by
  rw [tensorInducedMulRepHom, tensorInducedMulRepHom, ← Rep.ofHom_comp,
    U.tensorInducedMulIntertwiningMap_comp_changeTransversal R A s t]

/-- `Subgroup.tensorInducedMulRepHom` commutes with `Subgroup.tensorInducedChangeTransversal`
bundled via `Rep.mkIso` in `Rep R G`. -/
@[reassoc]
theorem mkIso_tensorInducedChangeTransversal_hom_tensorInducedMulRepHom
    (s t : U.LeftTransversal) [Fintype (G ⧸ U)] :
    (Rep.mkIso (U.tensorInducedChangeTransversal s t
        (Representation.ofDistribMulAction R U A))).hom ≫
      U.tensorInducedMulRepHom R A s =
      U.tensorInducedMulRepHom R A t := by
  rw [Rep.mkIso_hom, ofHom_tensorInducedChangeTransversal_tensorInducedMulRepHom]

end TwistedMultiplicationRep

end Subgroup

namespace TauCeti

/-! ### Worked examples -/

/-- With trivial action of `C₂` on `ℤ` and two cosets (`U = ⊥`), the tensor-induced action of the
nontrivial group element swaps `2 ⊗ 3` to `3 ⊗ 2`, and `Subgroup.tensorInducedMulAlgHom` sends
both pure tensors to `6` (`≠ 5`). -/
example :
    ∃ (G : Type) (_ : Group G) (U : Subgroup G) (_ : Fintype (G ⧸ U))
      (_ : MulSemiringAction G ℤ) (_ : SMulCommClass G ℤ ℤ)
      (s : U.LeftTransversal) (σ : G) (z₂₃ z₃₂ : ⨂[ℤ] _ : G ⧸ U, ℤ),
      U.tensorInducedAlgAut ℤ ℤ s σ z₂₃ = z₃₂ ∧
        U.tensorInducedMulAlgHom ℤ ℤ s z₂₃ = 6 ∧
        U.tensorInducedMulAlgHom ℤ ℤ s z₃₂ = 6 ∧
        (6 : ℤ) ≠ 5 := by
  let G := Multiplicative (ZMod 2)
  let U : Subgroup G := ⊥
  let : Fintype (G ⧸ U) := Fintype.ofEquiv G QuotientGroup.quotientBot.toEquiv.symm
  let : DecidableEq (G ⧸ U) := Equiv.decidableEq QuotientGroup.quotientBot.toEquiv
  let : MulSemiringAction G ℤ := MulSemiringAction.compHom ℤ (1 : G →* (ℤ ≃+* ℤ))
  have htriv : ∀ (g : G) (n : ℤ), g • n = n := fun g n ↦ by simp [MulAction.compHom_smul_def]
  have : SMulCommClass G ℤ ℤ := ⟨fun g m n ↦ by simp [htriv]⟩
  let s : U.LeftTransversal :=
    ⟨Set.range QuotientGroup.quotientBot,
      Subgroup.isComplement_range_left fun x ↦ QuotientGroup.induction_on x fun _ ↦ rfl⟩
  let σ : G := Multiplicative.ofAdd 1
  let z₂₃ : ⨂[ℤ] _ : G ⧸ U, ℤ :=
    PiTensorProduct.tprod ℤ fun x ↦ if QuotientGroup.quotientBot x = 1 then 2 else 3
  let z₃₂ : ⨂[ℤ] _ : G ⧸ U, ℤ :=
    PiTensorProduct.tprod ℤ fun x ↦ if QuotientGroup.quotientBot x = 1 then 3 else 2
  have htrivU : ∀ (u : U) (n : ℤ), u • n = n := fun u n ↦ by
    rw [Subgroup.smul_def]
    exact htriv u n
  refine ⟨G, inferInstance, U, inferInstance, inferInstance, inferInstance,
    s, σ, z₂₃, z₃₂, ?_, ?_, ?_, by decide⟩
  · simp only [z₂₃, z₃₂, Subgroup.tensorInducedAlgAut_tprod, htrivU]
    congr 1
    funext x
    refine QuotientGroup.induction_on x fun g ↦ ?_
    dsimp only [U]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff, Subgroup.mem_bot]
    fin_cases g <;> decide
  · rw [U.tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self ℤ ℤ s htriv,
      PiTensorProduct.mulAlgHom_tprod, ← Equiv.prod_comp QuotientGroup.quotientBot.toEquiv.symm]
    decide
  · rw [U.tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self ℤ ℤ s htriv,
      PiTensorProduct.mulAlgHom_tprod, ← Equiv.prod_comp QuotientGroup.quotientBot.toEquiv.symm]
    decide

/-- With one coset (`U = ⊤`) and representative `1`, `Subgroup.tensorInducedMulAlgHom` sends
`tprod R (fun _ ↦ a)` to `a` and `1` to `1`. -/
example {R G A : Type*} [CommSemiring R] [Group G] [CommSemiring A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] (a : A) :
    ∃ (U : Subgroup G) (_ : Fintype (G ⧸ U)) (_ : Subsingleton (G ⧸ U)) (s : U.LeftTransversal),
      U.leftTransversalRep s (QuotientGroup.mk 1) = 1 ∧
        U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R fun _ ↦ a) = a ∧
        U.tensorInducedMulAlgHom R A s 1 = 1 := by
  let U : Subgroup G := ⊤
  have : Subsingleton (G ⧸ U) :=
    ⟨fun x y ↦ QuotientGroup.induction_on x fun _ ↦
      QuotientGroup.induction_on y fun _ ↦ QuotientGroup.eq.mpr trivial⟩
  let : Fintype (G ⧸ U) := Fintype.ofSubsingleton (QuotientGroup.mk 1)
  let s : U.LeftTransversal :=
    ⟨Set.range fun _ : G ⧸ U ↦ (1 : G),
      Subgroup.isComplement_range_left fun _ ↦ Subsingleton.elim _ _⟩
  have hs : U.leftTransversalRep s (QuotientGroup.mk 1) = 1 :=
    congr_fun (Subgroup.leftTransversalRep_range U (fun _ : G ⧸ U ↦ (1 : G))
      fun _ ↦ Subsingleton.elim _ _) (QuotientGroup.mk 1)
  refine ⟨U, inferInstance, inferInstance, s, hs, ?_, ?_⟩
  · rw [U.tensorInducedMulAlgHom_eq_subsingletonAlgEquiv_of_rep_eq_one R A s
      (QuotientGroup.mk 1) hs]
    exact PiTensorProduct.subsingletonAlgEquiv_tprod (QuotientGroup.mk 1) _ _
  · exact map_one _

/-- For `A = ℤ[X]` with `C₂` acting by `X ↦ -X` and `U = ⊥`, Evens's twisted multiplication sends
`X ⊗ 1` to `X` and `1 ⊗ X` to `-X`, swapping the two tensor factors via
`Subgroup.tensorInducedAlgAut` agrees with the nontrivial group element's action on the target,
and untwisted `PiTensorProduct.mulAlgHom` instead sends both pure tensors to `X ≠ -X`. -/
example :
    ∃ (G : Type) (_ : Group G) (U : Subgroup G) (_ : Fintype (G ⧸ U))
      (_ : MulSemiringAction G (Polynomial ℤ)) (_ : SMulCommClass G ℤ (Polynomial ℤ))
      (s : U.LeftTransversal) (σ : G) (z₁ z₂ : ⨂[ℤ] _ : G ⧸ U, Polynomial ℤ),
      U.tensorInducedMulAlgHom ℤ (Polynomial ℤ) s z₁ = Polynomial.X ∧
        U.tensorInducedMulAlgHom ℤ (Polynomial ℤ) s z₂ = -Polynomial.X ∧
        U.tensorInducedAlgAut ℤ (Polynomial ℤ) s σ z₁ = z₂ ∧
        U.tensorInducedMulAlgHom ℤ (Polynomial ℤ) s
            (U.tensorInducedAlgAut ℤ (Polynomial ℤ) s σ z₁) =
          σ • U.tensorInducedMulAlgHom ℤ (Polynomial ℤ) s z₁ ∧
        PiTensorProduct.mulAlgHom (R := ℤ) z₁ = Polynomial.X ∧
        PiTensorProduct.mulAlgHom (R := ℤ) z₂ = Polynomial.X ∧
        (Polynomial.X : Polynomial ℤ) ≠ -Polynomial.X := by
  let G := Multiplicative (ZMod 2)
  let U : Subgroup G := ⊥
  let negX : Polynomial ℤ ≃ₐ[ℤ] Polynomial ℤ :=
    AlgEquiv.ofAlgHom (Polynomial.aeval (-Polynomial.X : Polynomial ℤ))
      (Polynomial.aeval (-Polynomial.X : Polynomial ℤ))
      (Polynomial.algHom_ext (by simp))
      (Polynomial.algHom_ext (by simp))
  have hsq : negX * negX = 1 := AlgEquiv.ext fun p ↦ by
    have hid : (Polynomial.aeval (-Polynomial.X : Polynomial ℤ)).comp
        (Polynomial.aeval (-Polynomial.X : Polynomial ℤ)) = AlgHom.id ℤ (Polynomial ℤ) :=
      Polynomial.algHom_ext (by simp)
    exact AlgHom.congr_fun hid p
  let actHom : G →* (Polynomial ℤ ≃ₐ[ℤ] Polynomial ℤ) :=
    { toFun g := if g = 1 then 1 else negX
      map_one' := ite_eq_left rfl
      map_mul' g h := by
        fin_cases g <;> fin_cases h <;> first | rfl | exact hsq.symm }
  let : MulSemiringAction G (Polynomial ℤ) := MulSemiringAction.compHom _ actHom
  have : SMulCommClass G ℤ (Polynomial ℤ) := ⟨fun g r p ↦ by
    simpa only [MulAction.compHom_smul_def, AlgEquiv.smul_def] using map_smul (actHom g) r p⟩
  let : Fintype (G ⧸ U) := Fintype.ofEquiv G QuotientGroup.quotientBot.toEquiv.symm
  let : DecidableEq (G ⧸ U) := Equiv.decidableEq QuotientGroup.quotientBot.toEquiv
  let hbot : ∀ u : G ⧸ U, (QuotientGroup.mk (QuotientGroup.quotientBot u) : G ⧸ U) = u :=
    fun u ↦ QuotientGroup.induction_on u fun _ ↦ rfl
  let s : U.LeftTransversal :=
    ⟨Set.range QuotientGroup.quotientBot, Subgroup.isComplement_range_left hbot⟩
  let σ : G := Multiplicative.ofAdd 1
  let x₀ : G ⧸ U := QuotientGroup.mk 1
  let x₁ : G ⧸ U := QuotientGroup.mk σ
  let z₁ : ⨂[ℤ] _ : G ⧸ U, Polynomial ℤ := PiTensorProduct.singleAlgHom x₀ Polynomial.X
  let z₂ : ⨂[ℤ] _ : G ⧸ U, Polynomial ℤ := PiTensorProduct.singleAlgHom x₁ Polynomial.X
  have hs_rep : ∀ g : G, U.leftTransversalRep s (QuotientGroup.mk g) = g := fun g ↦ by
    rw [Subgroup.leftTransversalRep_range U QuotientGroup.quotientBot hbot]
    rfl
  have hσ_ne : σ ≠ 1 := by decide
  have hσ_X : σ • (Polynomial.X : Polynomial ℤ) = -Polynomial.X := by
    simp [MulAction.compHom_smul_def, actHom, hσ_ne, negX]
  refine ⟨G, inferInstance, U, inferInstance, inferInstance, inferInstance,
    s, σ, z₁, z₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.tensorInducedMulAlgHom_singleAlgHom, hs_rep 1, one_smul]
  · rw [Subgroup.tensorInducedMulAlgHom_singleAlgHom, hs_rep σ, hσ_X]
  · simp only [z₁, z₂, x₀, x₁, Subgroup.tensorInducedAlgAut_singleAlgHom,
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    have hu : (U.monomialHom s σ).left (QuotientGroup.mk σ) = 1 := Subsingleton.elim _ _
    rw [hu, one_smul]
  · exact U.tensorInducedMulAlgHom_tensorInducedAlgAut ℤ (Polynomial ℤ) s σ z₁
  · exact PiTensorProduct.mulAlgHom_singleAlgHom x₀ Polynomial.X
  · exact PiTensorProduct.mulAlgHom_singleAlgHom x₁ Polynomial.X
  · intro h
    have h1 := congrArg (Polynomial.eval 1) h
    simp at h1

end TauCeti
