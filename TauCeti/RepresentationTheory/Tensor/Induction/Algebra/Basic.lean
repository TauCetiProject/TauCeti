/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Subobjects
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.RingTheory.PiTensorProduct.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The tensor-induced algebra and its equivariant multiplication

When a group `D` acts on an `R`-algebra `A` by `R`-algebra automorphisms, the wreath-product
representation `Representation.wreathTensor` on the indexed tensor power `⨂[R] _ : ι, A` acts by
`R`-algebra automorphisms (`TauCeti.WreathProduct.tensorAlgAut`): the top permutation reindexes the
factors via `PiTensorProduct.permAlgEquiv` and the base coordinates act slotwise via
`PiTensorProduct.congrAlgEquiv`.

Pulling this action back along the monomial homomorphism `Subgroup.monomialHom` of a subgroup
`U ≤ G` and a left transversal `s : U.LeftTransversal` equips the tensor-induced module
`⨂[R] _ : G ⧸ U, A` of a `U`-algebra `A` with an action of `G` by `R`-algebra automorphisms
(`Subgroup.tensorInducedAlgAut`, bundled as a `MulSemiringAction` in
`Subgroup.tensorInducedMulSemiringAction`) whose underlying linear operators agree with
`Subgroup.tensorInducedRepresentation`. Changing the transversal gives a `G`-equivariant
`R`-algebra isomorphism (`Subgroup.tensorInducedChangeTransversalAlgEquiv`) upgrading
`Subgroup.tensorInducedChangeTransversal`.

When `A` carries an action of the ambient group `G` by `R`-algebra automorphisms, applying the
chosen coset representatives slotwise gives an untwisting `R`-algebra equivalence
`Subgroup.tensorInducedUntwistAlgEquiv` on `⨂[R] _ : G ⧸ U, A`. It conjugates the monomial
`G`-action into the transversal-free action that permutes coset slots and applies `g` in every
factor. When `A` is commutative and `U` has finitely many left cosets (`[Fintype (G ⧸ U)]`),
multiplying the untwisted factors defines Evens' transversal multiplication
(`Subgroup.tensorInducedMulAlgHom`),

```text
⨂ₜ x, a x ↦ ∏ x : G ⧸ U, r_s(x) • a x,
```

built from `PiTensorProduct.productMap`. It is a `G`-equivariant `R`-algebra homomorphism from the
tensor-induced `G`-algebra to `A`, invariant under change of transversal and under group
homomorphisms that induce bijections of coset spaces. Specializing `R = ℤ` yields the
tensor-induced ring and `G`-ring multiplication of a commutative `G`-ring.

## Main definitions

* `TauCeti.WreathProduct.tensorAlgAut`: the homomorphism from `WreathProduct D ι` to the group of
  `R`-algebra automorphisms of `⨂[R] _ : ι, A`.
* `TauCeti.WreathProduct.tensorMulSemiringAction`: the corresponding `MulSemiringAction` on
  `⨂[R] _ : ι, A`.
* `Subgroup.tensorInducedAlgAut`: the homomorphism from `G` to the `R`-algebra automorphisms of
  `⨂[R] _ : G ⧸ U, A` along a left transversal.
* `Subgroup.tensorInducedMulSemiringAction`: the corresponding `MulSemiringAction` of `G`, whose
  underlying additive action agrees definitionally with `Subgroup.tensorInducedRepresentation`.
* `Subgroup.tensorInducedChangeTransversalAlgEquiv`: the `G`-equivariant `R`-algebra equivalence
  comparing two left transversals.
* `Subgroup.tensorInducedUntwistAlgEquiv`: the slotwise untwisting `R`-algebra equivalence
  `⨂ₜ x, a x ↦ ⨂ₜ x, r_s(x) • a x` for an ambient `G`-algebra `A`.
* `Subgroup.tensorInducedMulAlgHom`: the `G`-equivariant transversal multiplication
  `(⨂[R] _ : G ⧸ U, A) →ₐ[R] A` for a commutative `G`-algebra `A` and finite `G ⧸ U`.
* `Subgroup.tensorInducedMulIntertwiningMap`: `Subgroup.tensorInducedMulAlgHom` bundled as an
  intertwining map from the tensor-induced representation to `A`.
* `Subgroup.tensorInducedMulSubsingletonAlgEquiv`: the `R`-algebra equivalence
  `(⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A` obtained when `G ⧸ U` is a subsingleton (for instance `U = ⊤`).

## Main results

* `Subgroup.tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut`: changing the transversal
  intertwines the `G`-algebra actions.
* `Subgroup.tensorInducedUntwistAlgEquiv_tensorInducedAlgAut`: untwisting identifies the monomial
  `G`-action with coset permutation followed by the diagonal `G`-action.
* `Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut`: transversal multiplication is
  `G`-equivariant.
* `Subgroup.tensorInducedMulAlgHom_changeTransversalAlgEquiv`: transversal multiplication is
  independent of the chosen transversal up to `Subgroup.tensorInducedChangeTransversalAlgEquiv`.
* `Subgroup.tensorInducedMulAlgHom_reindexAlgEquiv`: transversal multiplication commutes with
  reindexing along a group homomorphism inducing a bijection of coset spaces.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 2--5, p. 60.
-/

public section

open scoped TensorProduct

universe u v v' w w' x

namespace TauCeti.WreathProduct

variable (R : Type u) (D : Type v) (A : Type w) (ι : Type x)
variable [CommSemiring R] [Group D] [Semiring A] [Algebra R A]
  [MulSemiringAction D A] [SMulCommClass D R A]

/-- The permutation wreath product `(ι → D) ⋊ Equiv.Perm ι` acts on the indexed tensor power
`⨂[R] _ : ι, A` by `R`-algebra automorphisms: the top permutation reindexes the factors and the
base coordinates act slotwise. -/
noncomputable def tensorAlgAut :
    WreathProduct D ι →* ((⨂[R] _ : ι, A) ≃ₐ[R] ⨂[R] _ : ι, A) where
  toFun a := (PiTensorProduct.permAlgEquiv (R := R) (ι := ι) A a.right).trans
    (PiTensorProduct.congrAlgEquiv fun i ↦ MulSemiringAction.toAlgEquiv R A (a.left i))
  map_one' := AlgEquiv.ext fun z ↦ by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r m => simp [Equiv.Perm.one_def]
    | add y z hy hz => simp only [map_add, hy, hz]
  map_mul' a b := AlgEquiv.ext fun z ↦ by
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      simp [PermutationWreathProduct.mul_left, Equiv.Perm.mul_def, mul_smul, Function.comp_def]
    | add y z hy hz => simp only [map_add, hy, hz]

variable {R D A ι}

/-- On a pure tensor, the wreath-product algebra automorphism reindexes the factors by the inverse
of the top permutation and applies the base group action in each coordinate. -/
@[simp]
theorem tensorAlgAut_tprod (a : WreathProduct D ι) (m : ι → A) :
    tensorAlgAut R D A ι a (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ a.left i • m (a.right.symm i) := by
  simp [tensorAlgAut, Function.comp_def]

/-- On a single-slot inclusion, the wreath-product algebra automorphism moves slot `i` to
`a.right i` and acts on the entry by `a.left (a.right i)`. It is a pre-simp lemma since
`singleAlgHom_apply` would otherwise expand the slot inclusion first. -/
@[simp↓]
theorem tensorAlgAut_singleAlgHom [DecidableEq ι] (a : WreathProduct D ι) (i : ι) (x : A) :
    tensorAlgAut R D A ι a (PiTensorProduct.singleAlgHom i x) =
      PiTensorProduct.singleAlgHom (a.right i) (a.left (a.right i) • x) := by
  simp only [tensorAlgAut, MonoidHom.coe_mk, OneHom.coe_mk, AlgEquiv.trans_apply,
    PiTensorProduct.permAlgEquiv_singleAlgHom, PiTensorProduct.congrAlgEquiv_singleAlgHom,
    MulSemiringAction.toAlgEquiv_apply]

/-- The base subgroup of the wreath product acts independently by algebra automorphisms in each
tensor factor. This derived normal form is an explicit rewrite lemma rather than a simp lemma, since
`tensorAlgAut_tprod` already simplifies its left-hand side. -/
theorem tensorAlgAut_inl_tprod (a : ι → D) (m : ι → A) :
    tensorAlgAut R D A ι (SemidirectProduct.inl a) (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ a i • m i := by
  simp [Equiv.Perm.one_def]

/-- The top symmetric subgroup of the wreath product acts by reindexing the tensor factors. This
derived normal form is an explicit rewrite lemma rather than a simp lemma, since
`tensorAlgAut_tprod` already proves it by simplification. -/
theorem tensorAlgAut_inr_tprod (σ : Equiv.Perm ι) (m : ι → A) :
    tensorAlgAut R D A ι (SemidirectProduct.inr σ) (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ m (σ.symm i) := by
  simp

/-- The underlying linear map of the wreath-product algebra automorphism is
`Representation.wreathTensor` of `Representation.ofDistribMulAction`. -/
@[simp]
theorem tensorAlgAut_toLinearMap (a : WreathProduct D ι) :
    (tensorAlgAut R D A ι a).toLinearMap =
      (Representation.ofDistribMulAction R D A).wreathTensor ι a := by
  ext m
  simp

/-- Pointwise agreement of `tensorAlgAut` with `Representation.wreathTensor`. -/
theorem tensorAlgAut_apply (a : WreathProduct D ι) (z : ⨂[R] _ : ι, A) :
    tensorAlgAut R D A ι a z =
      (Representation.ofDistribMulAction R D A).wreathTensor ι a z :=
  LinearMap.congr_fun (tensorAlgAut_toLinearMap a) z

variable (R D A ι) in
/-- The `MulSemiringAction` of `WreathProduct D ι` on `⨂[R] _ : ι, A` induced by a
`MulSemiringAction` of `D` on `A`. Its underlying `DistribMulAction` is definitionally
`DistribMulAction.compHom` of `Representation.wreathTensor`. It is a named definition rather than a
global instance so callers opt into it locally when unbundled `•` notation is desired. -/
@[expose, instance_reducible]
noncomputable def tensorMulSemiringAction :
    MulSemiringAction (WreathProduct D ι) (⨂[R] _ : ι, A) :=
  { DistribMulAction.compHom (⨂[R] _ : ι, A)
      ((Representation.ofDistribMulAction R D A).wreathTensor ι) with
    smul_one a := by
      -- Express the action via `tensorAlgAut`, which preserves `1` as an algebra equivalence.
      change (Representation.ofDistribMulAction R D A).wreathTensor ι a 1 = 1
      rw [← tensorAlgAut_apply, map_one]
    smul_mul a y z := by
      -- Express the action via `tensorAlgAut`, which preserves `*` as an algebra equivalence.
      change (Representation.ofDistribMulAction R D A).wreathTensor ι a (y * z) =
        (Representation.ofDistribMulAction R D A).wreathTensor ι a y *
          (Representation.ofDistribMulAction R D A).wreathTensor ι a z
      rw [← tensorAlgAut_apply, ← tensorAlgAut_apply, ← tensorAlgAut_apply, map_mul] }

variable (R D A ι) in
/-- The wreath-product action on `⨂[R] _ : ι, A` commutes with scalar multiplication by `R`. -/
theorem tensorSMulCommClass :
    letI := tensorMulSemiringAction R D A ι
    SMulCommClass (WreathProduct D ι) R (⨂[R] _ : ι, A) :=
  letI := tensorMulSemiringAction R D A ι
  ⟨fun a r z ↦ ((Representation.ofDistribMulAction R D A).wreathTensor ι a).map_smul r z⟩

end TauCeti.WreathProduct

namespace Subgroup

open TauCeti

/-! ### The tensor-induced `G`-algebra of a `U`-algebra -/

section TensorInducedAlgebra

variable {G : Type v} [Group G] (U : Subgroup G) (s t : U.LeftTransversal)
variable (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

/-- **Tensor induction on algebras**: for a subgroup `U ≤ G`, a left transversal `s`, and an
`R`-algebra `A` on which `U` acts by `R`-algebra automorphisms, `G` acts on the tensor-induced
algebra `⨂[R] _ : G ⧸ U, A` by `R`-algebra automorphisms via the monomial embedding
`Subgroup.monomialHom`. -/
noncomputable def tensorInducedAlgAut :
    G →* ((⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A) :=
  (WreathProduct.tensorAlgAut R U A (G ⧸ U)).comp (U.monomialHom s)

/-- The tensor-induced algebra automorphism is the wreath-product algebra automorphism evaluated at
the monomial image of `g`. -/
theorem tensorInducedAlgAut_def (g : G) :
    U.tensorInducedAlgAut s R A g =
      WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialHom s g) :=
  (rfl)

/-- The underlying linear map of `Subgroup.tensorInducedAlgAut` is
`Subgroup.tensorInducedRepresentation` on `Representation.ofDistribMulAction`. -/
@[simp]
theorem tensorInducedAlgAut_toLinearMap (g : G) :
    (U.tensorInducedAlgAut s R A g).toLinearMap =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g := by
  rw [tensorInducedAlgAut_def, WreathProduct.tensorAlgAut_toLinearMap]
  exact LinearMap.ext fun z ↦ (U.tensorInducedRepresentation_apply s _ g z).symm

/-- Pointwise agreement of `Subgroup.tensorInducedAlgAut` with
`Subgroup.tensorInducedRepresentation`. -/
theorem tensorInducedAlgAut_apply (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedAlgAut s R A g z =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z :=
  LinearMap.congr_fun (U.tensorInducedAlgAut_toLinearMap s R A g) z

/-- On a pure tensor, `Subgroup.tensorInducedAlgAut` translates coset coordinates by `g⁻¹` and
acts in slot `x` by the transversal word `(U.monomialHom s g).left x`. -/
@[simp]
theorem tensorInducedAlgAut_tprod (g : G) (m : G ⧸ U → A) :
    U.tensorInducedAlgAut s R A g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialHom s g).left x • m (g⁻¹ • x) := by
  rw [tensorInducedAlgAut_apply, tensorInducedRepresentation_apply_tprod]
  rfl

/-- On a single-slot inclusion at coset `x`, `Subgroup.tensorInducedAlgAut` moves the entry to coset
`g • x` and acts by `(U.monomialHom s g).left (g • x)`. -/
@[simp↓]
theorem tensorInducedAlgAut_singleAlgHom [DecidableEq (G ⧸ U)] (g : G) (x : G ⧸ U) (a : A) :
    U.tensorInducedAlgAut s R A g (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom (g • x) ((U.monomialHom s g).left (g • x) • a) := by
  rw [tensorInducedAlgAut_def, WreathProduct.tensorAlgAut_singleAlgHom, monomialHom_right]

/-- The tensor-induced representation of a `U`-algebra fixes the multiplicative unit
`1 = ⨂ₜ _, 1`. -/
@[simp]
theorem tensorInducedRepresentation_ofDistribMulAction_one (g : G) :
    U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g 1 = 1 := by
  rw [← tensorInducedAlgAut_apply, map_one]

/-- The tensor-induced representation of a `U`-algebra distributes over multiplication in
`⨂[R] _ : G ⧸ U, A`. -/
theorem tensorInducedRepresentation_ofDistribMulAction_mul (g : G) (y z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g (y * z) =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g y *
        U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z := by
  rw [← tensorInducedAlgAut_apply, ← tensorInducedAlgAut_apply, ← tensorInducedAlgAut_apply,
    map_mul]

/-- The `MulSemiringAction` of `G` on `⨂[R] _ : G ⧸ U, A` obtained by tensor induction along
`s`. Its underlying `DistribMulAction` is definitionally `DistribMulAction.compHom` of
`U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)`, matching the action
installed on `TauCeti.DiscreteRep.tensorInduced`. -/
@[expose, instance_reducible]
noncomputable def tensorInducedMulSemiringAction :
    MulSemiringAction G (⨂[R] _ : G ⧸ U, A) :=
  { DistribMulAction.compHom (⨂[R] _ : G ⧸ U, A)
      (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)) with
    smul_one g := U.tensorInducedRepresentation_ofDistribMulAction_one s R A g
    smul_mul g y z := U.tensorInducedRepresentation_ofDistribMulAction_mul s R A g y z }

/-- The tensor-induced `MulSemiringAction` commutes with scalar multiplication by `R`. -/
theorem tensorInducedSMulCommClass :
    letI := U.tensorInducedMulSemiringAction s R A
    SMulCommClass G R (⨂[R] _ : G ⧸ U, A) :=
  letI := U.tensorInducedMulSemiringAction s R A
  ⟨fun g r z ↦
    (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g).map_smul r z⟩

/-! ### Change of transversal as an isomorphism of `G`-algebras -/

/-- **Change of transversal on tensor-induced algebras**: the base-group comparison element
`Subgroup.monomialChangeTransversal` acts on `⨂[R] _ : G ⧸ U, A` as an `R`-algebra equivalence
intertwining the `G`-algebra actions attached to `t` and `s`. This upgrades
`Subgroup.tensorInducedChangeTransversalLinearEquiv` and
`Subgroup.tensorInducedChangeTransversal`. -/
noncomputable def tensorInducedChangeTransversalAlgEquiv :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A :=
  WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialChangeTransversal s t)

/-- The underlying linear equivalence of `Subgroup.tensorInducedChangeTransversalAlgEquiv` is
`Subgroup.tensorInducedChangeTransversalLinearEquiv`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_toLinearEquiv :
    (U.tensorInducedChangeTransversalAlgEquiv s t R A).toLinearEquiv =
      U.tensorInducedChangeTransversalLinearEquiv s t
        (Representation.ofDistribMulAction R U A) := by
  apply LinearEquiv.ext
  intro z
  rw [AlgEquiv.coe_toLinearEquiv, tensorInducedChangeTransversalAlgEquiv,
    WreathProduct.tensorAlgAut_apply, tensorInducedChangeTransversalLinearEquiv_apply]

/-- Pointwise agreement of `Subgroup.tensorInducedChangeTransversalAlgEquiv` with
`Subgroup.tensorInducedChangeTransversal`. -/
theorem tensorInducedChangeTransversalAlgEquiv_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A z =
      U.tensorInducedChangeTransversal s t (Representation.ofDistribMulAction R U A) z := by
  rw [tensorInducedChangeTransversal_apply,
    ← tensorInducedChangeTransversalAlgEquiv_toLinearEquiv]
  rfl

/-- On a pure tensor, changing the transversal applies the transversal difference in each coset
coordinate. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_tprod (m : G ⧸ U → A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialChangeTransversal s t).left x • m x := by
  rw [tensorInducedChangeTransversalAlgEquiv, WreathProduct.tensorAlgAut_tprod]
  simp [Equiv.Perm.one_def]

/-- On a single-slot inclusion, changing the transversal acts on that slot by the transversal
difference. -/
@[simp↓]
theorem tensorInducedChangeTransversalAlgEquiv_singleAlgHom [DecidableEq (G ⧸ U)]
    (x : G ⧸ U) (a : A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom x ((U.monomialChangeTransversal s t).left x • a) := by
  rw [tensorInducedChangeTransversalAlgEquiv, WreathProduct.tensorAlgAut_singleAlgHom,
    monomialChangeTransversal_right, Equiv.Perm.coe_one, id_eq]

/-- Comparing a transversal with itself gives the identity algebra equivalence. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_self :
    U.tensorInducedChangeTransversalAlgEquiv s s R A = AlgEquiv.refl := by
  rw [tensorInducedChangeTransversalAlgEquiv, monomialChangeTransversal_self, map_one]
  rfl

/-- Change-of-transversal algebra equivalences compose across an intermediate transversal. -/
theorem tensorInducedChangeTransversalAlgEquiv_trans (v : U.LeftTransversal) :
    (U.tensorInducedChangeTransversalAlgEquiv t v R A).trans
        (U.tensorInducedChangeTransversalAlgEquiv s t R A) =
      U.tensorInducedChangeTransversalAlgEquiv s v R A := by
  ext z
  simp only [AlgEquiv.trans_apply, tensorInducedChangeTransversalAlgEquiv]
  rw [← AlgEquiv.mul_apply, ← map_mul, monomialChangeTransversal_mul]

/-- Swapping the two transversals gives the inverse algebra equivalence. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_symm :
    (U.tensorInducedChangeTransversalAlgEquiv s t R A).symm =
      U.tensorInducedChangeTransversalAlgEquiv t s R A := by
  apply AlgEquiv.ext
  intro z
  apply (U.tensorInducedChangeTransversalAlgEquiv s t R A).injective
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.trans_apply,
    tensorInducedChangeTransversalAlgEquiv_trans, tensorInducedChangeTransversalAlgEquiv_self]
  rfl

/-- **Change of transversal is `G`-equivariant on tensor-induced algebras**: the comparison
`Subgroup.tensorInducedChangeTransversalAlgEquiv` intertwines the `G`-algebra actions attached to
`t` and `s`. -/
theorem tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut
    (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (U.tensorInducedAlgAut t R A g z) =
      U.tensorInducedAlgAut s R A g (U.tensorInducedChangeTransversalAlgEquiv s t R A z) := by
  simp only [tensorInducedChangeTransversalAlgEquiv, tensorInducedAlgAut_def]
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul,
    monomialChangeTransversal_mul_monomialHom]

end TensorInducedAlgebra

/-! ### Untwisting when `A` is an ambient `G`-algebra -/

section Untwist

variable {G : Type v} [Group G] (U : Subgroup G) (s t : U.LeftTransversal)
variable (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- **Slotwise untwisting of a tensor-induced `G`-algebra**: when `A` is already a `G`-algebra,
acting in coset slot `x` by the chosen representative `U.leftTransversalRep s x` defines an
`R`-algebra automorphism of `⨂[R] _ : G ⧸ U, A` that removes the transversal dependence from the
`G`-action (`Subgroup.tensorInducedUntwistAlgEquiv_tensorInducedAlgAut`). -/
noncomputable def tensorInducedUntwistAlgEquiv :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A :=
  PiTensorProduct.congrAlgEquiv fun x ↦
    MulSemiringAction.toAlgEquiv R A (U.leftTransversalRep s x)

/-- Untwisting acts in coset slot `x` of a pure tensor by `U.leftTransversalRep s x`. -/
@[simp]
theorem tensorInducedUntwistAlgEquiv_tprod (m : G ⧸ U → A) :
    U.tensorInducedUntwistAlgEquiv s R A (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ U.leftTransversalRep s x • m x :=
  PiTensorProduct.congrAlgEquiv_tprod _ m

/-- The inverse untwisting acts in coset slot `x` of a pure tensor by
`(U.leftTransversalRep s x)⁻¹`. -/
@[simp]
theorem tensorInducedUntwistAlgEquiv_symm_tprod (m : G ⧸ U → A) :
    (U.tensorInducedUntwistAlgEquiv s R A).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.leftTransversalRep s x)⁻¹ • m x := by
  apply (U.tensorInducedUntwistAlgEquiv s R A).injective
  simp [smul_inv_smul]

/-- Untwisting sends `a` in coset slot `x` to `U.leftTransversalRep s x • a` in slot `x`. -/
@[simp↓]
theorem tensorInducedUntwistAlgEquiv_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    U.tensorInducedUntwistAlgEquiv s R A (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom x (U.leftTransversalRep s x • a) := by
  rw [tensorInducedUntwistAlgEquiv, PiTensorProduct.congrAlgEquiv_singleAlgHom,
    MulSemiringAction.toAlgEquiv_apply]

/-- Untwisting absorbs the change-of-transversal algebra equivalence: applying the comparison from
`t` to `s` and then untwisting by `s` is untwisting by `t`. -/
@[simp]
theorem tensorInducedUntwistAlgEquiv_changeTransversalAlgEquiv (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedUntwistAlgEquiv s R A
        (U.tensorInducedChangeTransversalAlgEquiv s t R A z) =
      U.tensorInducedUntwistAlgEquiv t R A z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, tensorInducedChangeTransversalAlgEquiv_tprod,
      tensorInducedUntwistAlgEquiv_tprod]
    congr 2
    funext x
    rw [Subgroup.smul_def, monomialChangeTransversal_left, ← mul_smul,
      transversal_mul_transversalDiff]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- As composed algebra equivalences, change of transversal followed by untwisting gives untwisting
for the original transversal. -/
theorem tensorInducedChangeTransversalAlgEquiv_trans_untwist :
    (U.tensorInducedChangeTransversalAlgEquiv s t R A).trans
        (U.tensorInducedUntwistAlgEquiv s R A) =
      U.tensorInducedUntwistAlgEquiv t R A :=
  AlgEquiv.ext (U.tensorInducedUntwistAlgEquiv_changeTransversalAlgEquiv s t R A)

/-- **Untwisting removes the transversal from the `G`-algebra action**:
`tensorInducedUntwistAlgEquiv` intertwines `Subgroup.tensorInducedAlgAut` with the canonical
transversal-free action on `⨂[R] _ : G ⧸ U, A` that permutes coset factors by `g` and acts by `g`
in every factor. -/
theorem tensorInducedUntwistAlgEquiv_tensorInducedAlgAut (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedUntwistAlgEquiv s R A (U.tensorInducedAlgAut s R A g z) =
      PiTensorProduct.congrAlgEquiv (fun _ : G ⧸ U ↦ MulSemiringAction.toAlgEquiv R A g)
        (PiTensorProduct.permAlgEquiv A (MulAction.toPerm g)
          (U.tensorInducedUntwistAlgEquiv s R A z)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, tensorInducedAlgAut_tprod, tensorInducedUntwistAlgEquiv_tprod,
      PiTensorProduct.permAlgEquiv_tprod, PiTensorProduct.congrAlgEquiv_tprod,
      MulSemiringAction.toAlgEquiv_apply, Function.comp_def]
    congr 2
    funext x
    rw [Subgroup.smul_def, monomialHom_left, ← mul_smul, transversal_mul_lWord, mul_smul]
    rfl
  | add y z hy hz => simp only [map_add, hy, hz]

end Untwist

/-! ### Equivariant multiplication along a transversal -/

section Multiplication

variable {G : Type v} [Group G] (U : Subgroup G) (s t : U.LeftTransversal)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] [Fintype (G ⧸ U)]

/-- **Transversal multiplication on the tensor-induced algebra** (Evens, Section 5, p. 60): for a
commutative `G`-algebra `A` and a finite-index coset space `G ⧸ U`, the `R`-algebra homomorphism
`(⨂[R] _ : G ⧸ U, A) →ₐ[R] A` sending `⨂ₜ x, m x` to `∏ x : G ⧸ U, r_s(x) • m x`. -/
noncomputable def tensorInducedMulAlgHom : (⨂[R] _ : G ⧸ U, A) →ₐ[R] A :=
  PiTensorProduct.productMap fun x ↦ MulSemiringAction.toAlgHom R A (U.leftTransversalRep s x)

/-- Transversal multiplication sends a pure tensor `⨂ₜ x, m x` to the product over the cosets of
`r_s(x) • m x`. -/
@[simp]
theorem tensorInducedMulAlgHom_tprod (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • m x :=
  PiTensorProduct.productMap_tprod _ m

/-- Transversal multiplication sends `a` placed in coset slot `x` to `r_s(x) • a`. It is a
pre-simp lemma since `singleAlgHom_apply` would otherwise rewrite the slot inclusion first. -/
@[simp↓]
theorem tensorInducedMulAlgHom_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.singleAlgHom x a) =
      U.leftTransversalRep s x • a := by
  rw [tensorInducedMulAlgHom, PiTensorProduct.productMap_singleAlgHom,
    MulSemiringAction.toAlgHom_apply]

/-- Transversal multiplication factors as slotwise untwisting followed by ordinary factor
multiplication `PiTensorProduct.mulAlgHom`. -/
theorem mulAlgHom_tensorInducedUntwistAlgEquiv (z : ⨂[R] _ : G ⧸ U, A) :
    PiTensorProduct.mulAlgHom (U.tensorInducedUntwistAlgEquiv s R A z) =
      U.tensorInducedMulAlgHom s R A z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- As `R`-algebra homomorphisms, `PiTensorProduct.mulAlgHom` composed with
`Subgroup.tensorInducedUntwistAlgEquiv` is `Subgroup.tensorInducedMulAlgHom`. -/
theorem mulAlgHom_comp_tensorInducedUntwistAlgEquiv :
    (PiTensorProduct.mulAlgHom (R := R) (σ := G ⧸ U) (B := A)).comp
        (U.tensorInducedUntwistAlgEquiv s R A).toAlgHom =
      U.tensorInducedMulAlgHom s R A :=
  AlgHom.ext (U.mulAlgHom_tensorInducedUntwistAlgEquiv s R A)

/-- **Equivariance of transversal multiplication**: `Subgroup.tensorInducedMulAlgHom` is a
homomorphism of `G`-algebras from the tensor-induced algebra `⨂[R] _ : G ⧸ U, A` to `A`. -/
@[simp]
theorem tensorInducedMulAlgHom_tensorInducedAlgAut (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A (U.tensorInducedAlgAut s R A g z) =
      g • U.tensorInducedMulAlgHom s R A z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, smul_comm g r, tensorInducedAlgAut_tprod,
      tensorInducedMulAlgHom_tprod, tensorInducedMulAlgHom_tprod]
    congr 1
    have hcoord (x : G ⧸ U) :
        U.leftTransversalRep s x • ((U.monomialHom s g).left x • m (g⁻¹ • x)) =
          g • (U.leftTransversalRep s (g⁻¹ • x) • m (g⁻¹ • x)) := by
      rw [Subgroup.smul_def, monomialHom_left, ← mul_smul, transversal_mul_lWord, mul_smul]
    simp_rw [hcoord, ← MulSemiringAction.toAlgHom_apply R A g]
    rw [← map_prod, MulSemiringAction.toAlgHom_apply]
    exact congrArg (g • ·)
      (Equiv.prod_comp (MulAction.toPerm g⁻¹) fun x ↦ U.leftTransversalRep s x • m x)
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]

/-- Equivariance of `Subgroup.tensorInducedMulAlgHom`, phrased directly in terms of
`Subgroup.tensorInducedRepresentation`. -/
@[simp]
theorem tensorInducedMulAlgHom_tensorInducedRepresentation (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A
        (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z) =
      g • U.tensorInducedMulAlgHom s R A z := by
  rw [← tensorInducedAlgAut_apply, tensorInducedMulAlgHom_tensorInducedAlgAut]

/-- `Subgroup.tensorInducedMulAlgHom` bundled as a `G`-equivariant intertwining map from the
tensor-induced representation to `A`. -/
noncomputable def tensorInducedMulIntertwiningMap :
    (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)).IntertwiningMap
      (Representation.ofDistribMulAction R G A) where
  toLinearMap := (U.tensorInducedMulAlgHom s R A).toLinearMap
  isIntertwining' g := LinearMap.ext fun z ↦
    U.tensorInducedMulAlgHom_tensorInducedRepresentation s R A g z

/-- The underlying linear map of `Subgroup.tensorInducedMulIntertwiningMap` is that of
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_toLinearMap :
    (U.tensorInducedMulIntertwiningMap s R A).toLinearMap =
      (U.tensorInducedMulAlgHom s R A).toLinearMap :=
  (rfl)

/-- Applying `Subgroup.tensorInducedMulIntertwiningMap` evaluates
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulIntertwiningMap_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulIntertwiningMap s R A z = U.tensorInducedMulAlgHom s R A z :=
  (rfl)

/-- **Independence of transversal for multiplication**: changing the transversal via
`Subgroup.tensorInducedChangeTransversalAlgEquiv` commutes with
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulAlgHom_changeTransversalAlgEquiv (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A
        (U.tensorInducedChangeTransversalAlgEquiv s t R A z) =
      U.tensorInducedMulAlgHom t R A z := by
  rw [← mulAlgHom_tensorInducedUntwistAlgEquiv,
    tensorInducedUntwistAlgEquiv_changeTransversalAlgEquiv, mulAlgHom_tensorInducedUntwistAlgEquiv]

/-- As `R`-algebra homomorphisms, composing `Subgroup.tensorInducedMulAlgHom` with
`Subgroup.tensorInducedChangeTransversalAlgEquiv` gives the multiplication for the other
transversal. -/
theorem tensorInducedMulAlgHom_comp_changeTransversalAlgEquiv :
    (U.tensorInducedMulAlgHom s R A).comp
        (U.tensorInducedChangeTransversalAlgEquiv s t R A).toAlgHom =
      U.tensorInducedMulAlgHom t R A :=
  AlgHom.ext (U.tensorInducedMulAlgHom_changeTransversalAlgEquiv s t R A)

/-- Independence of transversal for `Subgroup.tensorInducedMulAlgHom`, phrased with the
representation equivalence `Subgroup.tensorInducedChangeTransversal`. -/
@[simp]
theorem tensorInducedMulAlgHom_changeTransversal (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom s R A
        (U.tensorInducedChangeTransversal s t (Representation.ofDistribMulAction R U A) z) =
      U.tensorInducedMulAlgHom t R A z := by
  rw [← tensorInducedChangeTransversalAlgEquiv_apply,
    tensorInducedMulAlgHom_changeTransversalAlgEquiv]

/-- When `G` acts trivially on `A`, transversal multiplication reduces to ordinary factor
multiplication `PiTensorProduct.mulAlgHom`. -/
theorem tensorInducedMulAlgHom_eq_mulAlgHom_of_smul_eq_self
    (hA : ∀ (g : G) (a : A), g • a = a) :
    U.tensorInducedMulAlgHom s R A = PiTensorProduct.mulAlgHom := by
  ext z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m => simp [hA]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- When `G` acts trivially on `A`, transversal multiplication sends the constant pure tensor
`⨂ₜ _, a` to `a ^ |G ⧸ U|`. -/
theorem tensorInducedMulAlgHom_tprod_const_of_smul_eq_self
    (hA : ∀ (g : G) (a : A), g • a = a) (a : A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ a) =
      a ^ Fintype.card (G ⧸ U) := by
  rw [tensorInducedMulAlgHom_tprod]
  simp [hA]

end Multiplication

/-! ### Naturality under group homomorphisms and canonical tensor reindexing -/

section Naturality

variable {R : Type u} [CommSemiring R]
  {G : Type v} [Group G] {G' : Type v'} [Group G']
  {U : Subgroup G} {U' : Subgroup G'} [Fintype (G ⧸ U)] [Fintype (G' ⧸ U')]
  {A : Type w} [CommSemiring A] [Algebra R A] [MulSemiringAction G A] [SMulCommClass G R A]
  {A' : Type w'} [CommSemiring A'] [Algebra R A'] [MulSemiringAction G' A'] [SMulCommClass G' R A']

/-- **Naturality of transversal multiplication under group homomorphisms**: if `φ : G →* G'`
induces a bijection `e : G ⧸ U ≃ G' ⧸ U'` of coset spaces and `f : A →ₐ[R] A'` intertwines
the actions along `φ`, then reindexing the tensor factors along `e` and applying `f` slotwise
carries transversal multiplication along `s` to transversal multiplication along `s.map φ e he`. -/
theorem tensorInducedMulAlgHom_map_reindexAlgEquiv
    (s : U.LeftTransversal) (φ : G →* G') (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (f : A →ₐ[R] A')
    (hf : ∀ (g : G) (a : A), f (g • a) = φ g • f a) (z : ⨂[R] _ : G ⧸ U, A) :
    U'.tensorInducedMulAlgHom (s.map φ e he) R A'
        (PiTensorProduct.map (fun _ : G' ⧸ U' ↦ f.toLinearMap)
          (PiTensorProduct.reindexAlgEquiv (fun _ : G ⧸ U ↦ A) e z)) =
      f (U.tensorInducedMulAlgHom s R A z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, PiTensorProduct.reindexAlgEquiv_tprod, PiTensorProduct.map_tprod,
      AlgHom.toLinearMap_apply, tensorInducedMulAlgHom_tprod, map_prod]
    congr 1
    refine (Equiv.prod_comp e fun y ↦
      U'.leftTransversalRep (s.map φ e he) y • f (m (e.symm y))).symm.trans ?_
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    rw [leftTransversalRep_map_apply, Equiv.symm_apply_apply, hf]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Reindexing tensor factors along an induced bijection of coset spaces preserves transversal
multiplication whenever the `G`-action on `A'` agrees with pullback along `φ`. -/
theorem tensorInducedMulAlgHom_reindexAlgEquiv [MulSemiringAction G A'] [SMulCommClass G R A']
    (s : U.LeftTransversal) (φ : G →* G') (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U'))
    (hφ : ∀ (g : G) (a : A'), g • a = φ g • a) (z : ⨂[R] _ : G ⧸ U, A') :
    U'.tensorInducedMulAlgHom (s.map φ e he) R A'
        (PiTensorProduct.reindexAlgEquiv (fun _ : G ⧸ U ↦ A') e z) =
      U.tensorInducedMulAlgHom s R A' z := by
  simpa only [AlgHom.toLinearMap_id, PiTensorProduct.map_id, LinearMap.id_apply, AlgHom.id_apply]
    using tensorInducedMulAlgHom_map_reindexAlgEquiv (R := R) (U := U) (U' := U') (A := A')
      (A' := A') s φ e he (AlgHom.id R A') hφ z

end Naturality

/-! ### Diagonal invariant tensors, index one, and index two -/

section Diagonal

variable {R : Type u} [CommRing R] {G : Type v} [Group G] (U : Subgroup G) (s : U.LeftTransversal)
variable (A : Type w) [CommRing A] [Algebra R A] [MulSemiringAction G A] [SMulCommClass G R A]
  [Fintype (G ⧸ U)]

/-- On the diagonal invariant tensor `Representation.tensorInducedDiagonal` of a `U`-invariant
element `a ∈ A`, transversal multiplication evaluates to the multiplicative norm
`∏ x : G ⧸ U, r_s(x) • a`. -/
theorem tensorInducedMulAlgHom_tensorInducedDiagonal
    (a : (Representation.ofDistribMulAction R U A).invariants) :
    U.tensorInducedMulAlgHom s R A
        ((Representation.ofDistribMulAction R U A).tensorInducedDiagonal s a) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • (a : A) := by
  simp [Representation.coe_tensorInducedDiagonal]

end Diagonal

section Subsingleton

variable {G : Type v} [Group G] (U : Subgroup G) (s : U.LeftTransversal)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] [Fintype (G ⧸ U)] [Subsingleton (G ⧸ U)]

/-- **One-coset algebra isomorphism**: when `G ⧸ U` is a subsingleton (for instance `U = ⊤`),
transversal multiplication is an `R`-algebra equivalence `(⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A`. -/
noncomputable def tensorInducedMulSubsingletonAlgEquiv :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (U.tensorInducedMulAlgHom s R A)
    ((PiTensorProduct.singleAlgHom (R := R) (A := fun _ : G ⧸ U ↦ A) (QuotientGroup.mk 1)).comp
      (MulSemiringAction.toAlgHom R A (U.leftTransversalRep s (QuotientGroup.mk 1))⁻¹))
    (AlgHom.ext fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, MulSemiringAction.toAlgHom_apply,
        tensorInducedMulAlgHom_singleAlgHom, smul_inv_smul])
    (by
      refine PiTensorProduct.algHom_ext fun x ↦ AlgHom.ext fun a ↦ ?_
      obtain rfl : x = QuotientGroup.mk 1 := Subsingleton.elim x _
      simp only [AlgHom.comp_apply, AlgHom.id_apply, tensorInducedMulAlgHom_singleAlgHom,
        MulSemiringAction.toAlgHom_apply, inv_smul_smul])

/-- The forward algebra map of `Subgroup.tensorInducedMulSubsingletonAlgEquiv` is
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulSubsingletonAlgEquiv_toAlgHom :
    (U.tensorInducedMulSubsingletonAlgEquiv s R A).toAlgHom =
      U.tensorInducedMulAlgHom s R A :=
  (rfl)

/-- Applying `Subgroup.tensorInducedMulSubsingletonAlgEquiv` evaluates
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulSubsingletonAlgEquiv_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulSubsingletonAlgEquiv s R A z =
      U.tensorInducedMulAlgHom s R A z :=
  (rfl)

/-- When `G ⧸ U` has one coset and its chosen representative is `1`, transversal multiplication
sends the pure tensor with entry `a` to `a`. -/
theorem tensorInducedMulAlgHom_tprod_of_subsingleton
    (hs : U.leftTransversalRep s (QuotientGroup.mk 1) = 1) (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) = m (QuotientGroup.mk 1) := by
  rw [tensorInducedMulAlgHom_tprod, Finset.prod_eq_single (QuotientGroup.mk 1)
    (fun x _ hx ↦ absurd (Subsingleton.elim x _) hx) (by simp), hs, one_smul]

end Subsingleton

section IndexTwo

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] [Fintype (G ⧸ U)]

/-- For a subgroup `U` of index two and `g ∉ U`, transversal multiplication on a pure tensor is
the product of the two coset terms at `⟦1⟧` and `⟦g⟧`. -/
theorem tensorInducedMulAlgHom_tprod_of_index_two (s : U.LeftTransversal)
    (hU : U.index = 2) {g : G} (hg : g ∉ U) (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) =
      (U.leftTransversalRep s (QuotientGroup.mk 1) • m (QuotientGroup.mk 1)) *
        (U.leftTransversalRep s (QuotientGroup.mk g) • m (QuotientGroup.mk g)) := by
  rw [tensorInducedMulAlgHom_tprod]
  exact Fintype.prod_eq_mul (QuotientGroup.mk 1) (QuotientGroup.mk g)
    (mk_ne_mk_one_of_notMem hg).symm fun u hu ↦
      ((eq_mk_one_or_eq_mk_of_index_two hU hg u).elim hu.1 hu.2).elim

/-- For a left transversal of an index-two subgroup `U` whose representatives at `⟦1⟧` and `⟦g⟧`
are `1` and `g`, transversal multiplication sends `⨂ₜ m` to `m ⟦1⟧ * g • m ⟦g⟧`. -/
theorem tensorInducedMulAlgHom_tprod_of_index_two_of_eq (s : U.LeftTransversal)
    (hU : U.index = 2) {g : G} (hg : g ∉ U)
    (h1 : U.leftTransversalRep s (QuotientGroup.mk 1) = 1)
    (hg' : U.leftTransversalRep s (QuotientGroup.mk g) = g) (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom s R A (PiTensorProduct.tprod R m) =
      m (QuotientGroup.mk 1) * g • m (QuotientGroup.mk g) := by
  rw [tensorInducedMulAlgHom_tprod_of_index_two U R A s hU hg m, h1, one_smul, hg']

end IndexTwo

end Subgroup

/-! ### Concrete checks -/

section Examples

open Polynomial

private abbrev TwoGroup := Multiplicative (ZMod 2)

private def twoGroupGen : TwoGroup := Multiplicative.ofAdd 1

private theorem bot_index_twoGroup : (⊥ : Subgroup TwoGroup).index = 2 := by
  rw [Subgroup.index_bot]
  exact Nat.card_zmod 2

private theorem twoGroupGen_notMem_bot : twoGroupGen ∉ (⊥ : Subgroup TwoGroup) := by
  rw [Subgroup.mem_bot]
  decide

private noncomputable def twoGroupBotTransversal : (⊥ : Subgroup TwoGroup).LeftTransversal :=
  ⟨Set.range ((⊥ : Subgroup TwoGroup).indexTwoTransversal twoGroupGen),
    Subgroup.isComplement_range_left
      (Subgroup.indexTwoTransversal_mk bot_index_twoGroup twoGroupGen_notMem_bot)⟩

private theorem twoGroupBotTransversal_rep :
    (⊥ : Subgroup TwoGroup).leftTransversalRep twoGroupBotTransversal =
      (⊥ : Subgroup TwoGroup).indexTwoTransversal twoGroupGen :=
  (⊥ : Subgroup TwoGroup).leftTransversalRep_range _
    (Subgroup.indexTwoTransversal_mk bot_index_twoGroup twoGroupGen_notMem_bot)

open Classical in
private theorem twoGroupBotTransversal_tprod {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [MulSemiringAction TwoGroup A] [SMulCommClass TwoGroup R A]
    (m : TwoGroup ⧸ (⊥ : Subgroup TwoGroup) → A) :
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal R A
        (PiTensorProduct.tprod R m) =
      m (QuotientGroup.mk 1) * twoGroupGen • m (QuotientGroup.mk twoGroupGen) :=
  (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom_tprod_of_index_two_of_eq R A
    twoGroupBotTransversal bot_index_twoGroup twoGroupGen_notMem_bot
    (by rw [twoGroupBotTransversal_rep, Subgroup.indexTwoTransversal_mk_one])
    (by rw [twoGroupBotTransversal_rep, Subgroup.indexTwoTransversal_of_ne twoGroupGen
      (TauCeti.mk_ne_mk_one_of_notMem twoGroupGen_notMem_bot)]) m

open Classical in
/-- Check 1: with trivial action of `C₂` on `ℤ` and two coset factors (`U = ⊥`), transversal
multiplication sends both `2 ⊗ 3` and its swapped tensor `3 ⊗ 2` to `6`. -/
example :
    letI : MulSemiringAction TwoGroup ℤ :=
      MulSemiringAction.compHom ℤ (1 : TwoGroup →* (ℤ →+* ℤ))
    let v₂₃ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup) → ℤ :=
      fun x ↦ if x = QuotientGroup.mk 1 then 2 else 3
    let swap : Equiv.Perm (TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) :=
      Equiv.swap (QuotientGroup.mk 1) (QuotientGroup.mk twoGroupGen)
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal ℤ ℤ
        (PiTensorProduct.tprod ℤ v₂₃) = 6 ∧
      (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal ℤ ℤ
        (PiTensorProduct.permAlgEquiv ℤ swap (PiTensorProduct.tprod ℤ v₂₃)) = 6 := by
  let _ : MulSemiringAction TwoGroup ℤ :=
    MulSemiringAction.compHom ℤ (1 : TwoGroup →* (ℤ →+* ℤ))
  intro v₂₃ swap
  have hne : (QuotientGroup.mk twoGroupGen : TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) ≠
      QuotientGroup.mk 1 :=
    TauCeti.mk_ne_mk_one_of_notMem twoGroupGen_notMem_bot
  have hsmul : ∀ (g : TwoGroup) (n : ℤ), g • n = n := fun _ _ ↦ rfl
  constructor
  · rw [twoGroupBotTransversal_tprod, hsmul]
    dsimp only [v₂₃]
    simp only [hne, ↓reduceIte]
    norm_num
  · rw [PiTensorProduct.permAlgEquiv_tprod, twoGroupBotTransversal_tprod, hsmul]
    dsimp only [v₂₃, swap, Function.comp_def]
    rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp only [hne, ↓reduceIte]
    norm_num

/-- Check 2: for one coset (`U = ⊤`) with chosen representative `1`, transversal multiplication
sends `a` to `a` and `1` to `1`. -/
example {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A] (a : A) :
    letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    letI : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofSubsingleton (QuotientGroup.mk 1)
    let s : (⊤ : Subgroup G).LeftTransversal :=
      ⟨Set.range fun _ : G ⧸ (⊤ : Subgroup G) ↦ (1 : G),
        Subgroup.isComplement_range_left fun x ↦ Subsingleton.elim _ x⟩
    (⊤ : Subgroup G).tensorInducedMulAlgHom s ℤ A
        (PiTensorProduct.tprod ℤ fun _ ↦ a) = a ∧
      (⊤ : Subgroup G).tensorInducedMulAlgHom s ℤ A 1 = 1 := by
  let _ : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  let _ : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofSubsingleton (QuotientGroup.mk 1)
  intro s
  have hs : (⊤ : Subgroup G).leftTransversalRep s (QuotientGroup.mk 1) = 1 := by
    have hrep := (⊤ : Subgroup G).leftTransversalRep_range
      (fun _ : G ⧸ (⊤ : Subgroup G) ↦ (1 : G)) (fun x ↦ Subsingleton.elim _ x)
    exact congrFun hrep (QuotientGroup.mk 1)
  exact ⟨(⊤ : Subgroup G).tensorInducedMulAlgHom_tprod_of_subsingleton s ℤ A hs _,
    map_one _⟩

private noncomputable def negXAlgEquiv : ℤ[X] ≃ₐ[ℤ] ℤ[X] :=
  AlgEquiv.ofAlgHom (aeval (-X : ℤ[X])) (aeval (-X : ℤ[X]))
    (Polynomial.algHom_ext <| by simp)
    (Polynomial.algHom_ext <| by simp)

private noncomputable def twoGroupPolyAct : TwoGroup →* (ℤ[X] →+* ℤ[X]) where
  toFun g := if g.toAdd = 0 then RingHom.id ℤ[X] else negXAlgEquiv.toAlgHom.toRingHom
  map_one' := rfl
  map_mul' g h := by
    by_cases hg : g.toAdd = 0
    · simp [toAdd_mul, hg, ← RingHom.one_def]
    · by_cases hh : h.toAdd = 0
      · simp [toAdd_mul, hh, ← RingHom.one_def]
      · have hgh : (g * h).toAdd = 0 := by
          revert hg hh g h
          decide
        simp only [hgh, hg, hh, ↓reduceIte]
        refine RingHom.ext fun p ↦ ?_
        -- Multiplication in `ℤ[X] →+* ℤ[X]` is composition of ring homomorphisms.
        change RingHom.id ℤ[X] p = negXAlgEquiv (negXAlgEquiv p)
        exact (negXAlgEquiv.symm_apply_apply p).symm

open Classical in
/-- Check 3: on `A = ℤ[X]` with `C₂` acting by `X ↦ -X` and `U = ⊥`, multiplication along
`{1, σ}` sends `X ⊗ 1` to `X` and `1 ⊗ X` to `-X`, and swapping the two tensor factors agrees
with acting by `σ` on `ℤ[X]`. -/
example :
    letI : MulSemiringAction TwoGroup ℤ[X] := MulSemiringAction.compHom ℤ[X] twoGroupPolyAct
    let xLeft : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X] :=
      PiTensorProduct.tprod ℤ fun x ↦ if x = QuotientGroup.mk 1 then X else 1
    let xRight : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X] :=
      PiTensorProduct.tprod ℤ fun x ↦ if x = QuotientGroup.mk 1 then 1 else X
    let swap : Equiv.Perm (TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) :=
      Equiv.swap (QuotientGroup.mk 1) (QuotientGroup.mk twoGroupGen)
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal ℤ ℤ[X] xLeft = X ∧
      (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal ℤ ℤ[X]
          xRight = -X ∧
      ∀ z : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X],
        (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom twoGroupBotTransversal ℤ ℤ[X]
            (PiTensorProduct.permAlgEquiv ℤ[X] swap z) =
          twoGroupGen •
            (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom
              twoGroupBotTransversal ℤ ℤ[X] z := by
  let _ : MulSemiringAction TwoGroup ℤ[X] := MulSemiringAction.compHom ℤ[X] twoGroupPolyAct
  intro xLeft xRight swap
  have hne : (QuotientGroup.mk twoGroupGen : TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) ≠
      QuotientGroup.mk 1 :=
    TauCeti.mk_ne_mk_one_of_notMem twoGroupGen_notMem_bot
  have hσX : twoGroupGen • (X : ℤ[X]) = -X := by
    -- Unfold the action through `MulSemiringAction.compHom` to evaluate `twoGroupPolyAct`.
    change twoGroupPolyAct twoGroupGen X = -X
    simp [twoGroupPolyAct, twoGroupGen, negXAlgEquiv]
  have hσ1 : twoGroupGen • (1 : ℤ[X]) = 1 := smul_one twoGroupGen
  refine ⟨?_, ?_, fun z ↦ ?_⟩
  · dsimp only [xLeft]
    rw [twoGroupBotTransversal_tprod]
    simp only [hne, ↓reduceIte, hσ1, mul_one]
  · dsimp only [xRight]
    rw [twoGroupBotTransversal_tprod]
    simp only [hne, ↓reduceIte, hσX, one_mul]
  · -- For `U = ⊥`, every transversal word lies in `⊥` and is `1`, while `σ` swaps the cosets.
    have hperm : PiTensorProduct.permAlgEquiv (R := ℤ) ℤ[X] swap z =
        (⊥ : Subgroup TwoGroup).tensorInducedAlgAut
          twoGroupBotTransversal ℤ ℤ[X] twoGroupGen z := by
      induction z using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        simp only [map_smul, PiTensorProduct.permAlgEquiv_tprod, Subgroup.tensorInducedAlgAut_tprod,
          Function.comp_def]
        dsimp only [swap]
        rw [Equiv.symm_swap]
        congr 2
        funext x
        have hu :
            ((⊥ : Subgroup TwoGroup).monomialHom twoGroupBotTransversal twoGroupGen).left x = 1 :=
          Subsingleton.elim _ _
        rw [hu, one_smul]
        rcases TauCeti.eq_mk_one_or_eq_mk_of_index_two bot_index_twoGroup
          twoGroupGen_notMem_bot x with rfl | rfl
        · rw [Equiv.swap_apply_left,
            TauCeti.smul_mk_one_of_notMem_of_index_two bot_index_twoGroup
              twoGroupGen_notMem_bot (mt (⊥ : Subgroup TwoGroup).inv_mem_iff.1
                twoGroupGen_notMem_bot)]
        · rw [Equiv.swap_apply_right,
            TauCeti.smul_mk_of_notMem_of_index_two bot_index_twoGroup
              twoGroupGen_notMem_bot (mt (⊥ : Subgroup TwoGroup).inv_mem_iff.1
                twoGroupGen_notMem_bot)]
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [hperm, Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut]

end Examples
