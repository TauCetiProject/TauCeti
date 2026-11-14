/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.GroupTheory.GroupAction.Hom
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Basic

/-!
# Tensor-induced `G`-algebras

When a group `D` acts on an `R`-algebra `A` by `R`-algebra automorphisms, the permutation wreath
product `WreathProduct D ι` acts on the indexed tensor power `⨂[R] _ : ι, A` by `R`-algebra
automorphisms: the top permutation reindexes the tensor factors via
`PiTensorProduct.reindexAlgEquiv` and the base coordinates act slotwise via
`PiTensorProduct.congrAlgEquiv`. Pulling this action back along `Subgroup.monomialHom s` for a
subgroup `U ≤ G` and a left transversal `s : U.LeftTransversal` makes the coset-indexed tensor
power `⨂[R] _ : G ⧸ U, A` a `G`-algebra, bundled as `Subgroup.TensorInduced U s R A`.

Evens' `G`-equivariant twisted multiplication on tensor-induced commutative `G`-algebras is
constructed in `TauCeti.RepresentationTheory.Tensor.Induction.Algebra.Multiplication`.

## Main definitions

* `TauCeti.WreathProduct.tensorAlgEquiv`, `TauCeti.WreathProduct.tensorAlgAut`: the action of the
  permutation wreath product `WreathProduct D ι` on `⨂[R] _ : ι, A` by `R`-algebra automorphisms.
* `Subgroup.tensorInducedAlgAut`: the `G`-action by `R`-algebra automorphisms on
  `⨂[R] _ : G ⧸ U, A` attached to `s : U.LeftTransversal`.
* `Subgroup.tensorInducedChangeTransversalAlgEquiv`: the `G`-equivariant `R`-algebra isomorphism
  comparing two left transversals.
* `Subgroup.tensorInducedTransitivityAlgEquiv`: the `R`-algebra isomorphism flattening iterated
  tensor induction along a tower `V ≤ U ≤ G`.
* `Subgroup.TensorInduced`: the tensor-induced carrier `⨂[R] _ : G ⧸ U, A` bundled with its
  `Semiring`, `Ring`, `CommSemiring`, `CommRing`, `Algebra R`, and `MulSemiringAction G` instances,
  together with `Subgroup.TensorInduced.representationEquiv`,
  `Subgroup.TensorInduced.repIsoTensorInductionFunctor`,
  `Subgroup.TensorInduced.changeTransversalAlgEquiv`, and
  `Subgroup.TensorInduced.changeTransversalMulSemiringActionHom`.

## Main results

* `TauCeti.WreathProduct.tensorAlgAut_toLinearMap`,
  `Subgroup.tensorInducedAlgAut_toLinearMap`: compatibility with `Representation.wreathTensor` and
  `Subgroup.tensorInducedRepresentation`.
* `Subgroup.tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut`,
  `Subgroup.TensorInduced.changeTransversalAlgEquiv_smul`: changing the left transversal
  intertwines the tensor-induced `G`-algebra actions.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society **108** (1963), §§2–5, pp. 56–60.
-/

public section

open scoped TensorProduct

universe u v w x

namespace TauCeti.WreathProduct

section AlgebraAction

variable (R : Type u) {D : Type v} (A : Type w) (ι : Type x)
  [CommSemiring R] [Group D] [Semiring A] [Algebra R A]
  [MulSemiringAction D A] [SMulCommClass D R A]

/-- An element `w` of the permutation wreath product `WreathProduct D ι` acts on the tensor power
`⨂[R] _ : ι, A` as an `R`-algebra automorphism: it reindexes the factors by `w.right` and applies
`w.left i` in slot `i`. -/
noncomputable def tensorAlgEquiv (w : WreathProduct D ι) :
    (⨂[R] _ : ι, A) ≃ₐ[R] ⨂[R] _ : ι, A :=
  (PiTensorProduct.reindexAlgEquiv (R := R) (fun _ : ι ↦ A) w.right).trans
    (PiTensorProduct.congrAlgEquiv fun i ↦ MulSemiringAction.toAlgEquiv R A (w.left i))

/-- On a pure tensor, `tensorAlgEquiv` permutes coordinates by `w.right⁻¹` and acts slotwise by
`w.left`. -/
@[simp]
theorem tensorAlgEquiv_tprod (w : WreathProduct D ι) (m : ι → A) :
    tensorAlgEquiv R A ι w (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ w.left i • m (w.right.symm i) := by
  simp [tensorAlgEquiv]

/-- The underlying `R`-linear map of `tensorAlgEquiv` is `Representation.wreathTensor` of the
`D`-action on `A`. -/
@[simp]
theorem tensorAlgEquiv_toLinearMap (w : WreathProduct D ι) :
    (tensorAlgEquiv R A ι w).toLinearEquiv.toLinearMap =
      (Representation.ofDistribMulAction R D A).wreathTensor ι w := by
  ext m
  simp [tensorAlgEquiv, Representation.wreathTensor_apply_tprod]

variable (D) in
/-- The group homomorphism from `WreathProduct D ι` to the `R`-algebra automorphism group of the
indexed tensor power `⨂[R] _ : ι, A`. -/
noncomputable def tensorAlgAut :
    WreathProduct D ι →* ((⨂[R] _ : ι, A) ≃ₐ[R] ⨂[R] _ : ι, A) where
  toFun := tensorAlgEquiv R A ι
  map_one' := AlgEquiv.ext fun x ↦ by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m => simp [Equiv.Perm.one_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  map_mul' w₁ w₂ := AlgEquiv.ext fun x ↦ by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      simp only [AlgEquiv.mul_apply, map_smul, tensorAlgEquiv_tprod,
        PermutationWreathProduct.mul_left, SemidirectProduct.mul_right, Equiv.Perm.mul_def,
        Equiv.symm_trans_apply, Equiv.Perm.smul_def, Equiv.Perm.inv_def, mul_smul]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Evaluating `tensorAlgAut` gives `tensorAlgEquiv`. -/
theorem tensorAlgAut_apply (w : WreathProduct D ι) :
    tensorAlgAut R D A ι w = tensorAlgEquiv R A ι w := (rfl)

/-- The underlying `R`-linear map of `tensorAlgAut` at `w` is `Representation.wreathTensor`. -/
@[simp]
theorem tensorAlgAut_toLinearMap (w : WreathProduct D ι) :
    (tensorAlgAut R D A ι w).toLinearEquiv.toLinearMap =
      (Representation.ofDistribMulAction R D A).wreathTensor ι w :=
  tensorAlgEquiv_toLinearMap R A ι w

/-- On a pure tensor, `tensorAlgAut` permutes coordinates by `w.right⁻¹` and acts slotwise by
`w.left`. -/
@[simp]
theorem tensorAlgAut_apply_tprod (w : WreathProduct D ι) (m : ι → A) :
    tensorAlgAut R D A ι w (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ w.left i • m (w.right.symm i) :=
  tensorAlgEquiv_tprod R A ι w m

/-- On pure tensors, the wreath-product algebra action agrees with the wreath-product action
`WreathProduct.product_smul` on `ι → A`. -/
theorem tensorAlgAut_apply_tprod_eq_smul (w : WreathProduct D ι) (m : ι → A) :
    tensorAlgAut R D A ι w (PiTensorProduct.tprod R m) = PiTensorProduct.tprod R (w • m) := by
  rw [tensorAlgAut_apply_tprod]
  rfl

/-- `tensorAlgAut` moves the factor inclusion at `i` to slot `w.right i` and acts on its entry by
`w.left (w.right i)`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise unfold the
factor inclusion first. -/
@[simp↓]
theorem tensorAlgAut_singleAlgHom [DecidableEq ι] (w : WreathProduct D ι) (i : ι) (a : A) :
    tensorAlgAut R D A ι w (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom (w.right i) (w.left (w.right i) • a) := by
  rw [tensorAlgAut_apply, tensorAlgEquiv, AlgEquiv.trans_apply,
    PiTensorProduct.reindexAlgEquiv_singleAlgHom, PiTensorProduct.congrAlgEquiv_singleAlgHom]
  rfl

end AlgebraAction

end TauCeti.WreathProduct

namespace Subgroup

open TauCeti

section TensorInducedAlgAut

variable {G : Type v} [Group G] (U : Subgroup G) (s : U.LeftTransversal)
  (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

/-- The tensor-induced action of `G` on `⨂[R] _ : G ⧸ U, A` by `R`-algebra automorphisms, obtained
by pulling back `TauCeti.WreathProduct.tensorAlgAut` along `U.monomialHom s`. -/
noncomputable def tensorInducedAlgAut :
    G →* ((⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A) :=
  (WreathProduct.tensorAlgAut R U A (G ⧸ U)).comp (U.monomialHom s)

/-- `tensorInducedAlgAut` evaluates the wreath-product algebra automorphism at
`U.monomialHom s g`. -/
theorem tensorInducedAlgAut_apply (g : G) :
    U.tensorInducedAlgAut s R A g =
      WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialHom s g) := (rfl)

/-- The underlying `R`-linear map of `U.tensorInducedAlgAut s R A g` is
`U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g`. -/
@[simp]
theorem tensorInducedAlgAut_toLinearMap (g : G) :
    (U.tensorInducedAlgAut s R A g).toLinearEquiv.toLinearMap =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g := by
  apply LinearMap.ext
  intro z
  rw [tensorInducedAlgAut_apply, WreathProduct.tensorAlgAut_toLinearMap]
  exact (U.tensorInducedRepresentation_apply s (Representation.ofDistribMulAction R U A) g z).symm

/-- Applying `U.tensorInducedAlgAut` agrees elementwise with `U.tensorInducedRepresentation`. -/
theorem tensorInducedAlgAut_apply_eq_tensorInducedRepresentation (g : G)
    (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedAlgAut s R A g z =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z :=
  LinearMap.congr_fun (U.tensorInducedAlgAut_toLinearMap s R A g) z

/-- On a pure tensor, `U.tensorInducedAlgAut` translates the coset coordinates by `g⁻¹` and acts
at `x` by the transversal word `(U.monomialHom s g).left x`. -/
@[simp]
theorem tensorInducedAlgAut_apply_tprod (g : G) (m : G ⧸ U → A) :
    U.tensorInducedAlgAut s R A g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialHom s g).left x • m (g⁻¹ • x) := by
  rw [tensorInducedAlgAut_apply_eq_tensorInducedRepresentation,
    tensorInducedRepresentation_apply_tprod]
  rfl

/-- `U.tensorInducedAlgAut` moves a factor inclusion at coset `x` to coset `g • x` and acts by the
transversal word at `g • x`. It is a pre-simp lemma since `singleAlgHom_apply` would otherwise
unfold the factor inclusion first. -/
@[simp↓]
theorem tensorInducedAlgAut_singleAlgHom [DecidableEq (G ⧸ U)] (g : G) (x : G ⧸ U) (a : A) :
    U.tensorInducedAlgAut s R A g (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom (g • x) ((U.monomialHom s g).left (g • x) • a) := by
  rw [tensorInducedAlgAut_apply, WreathProduct.tensorAlgAut_singleAlgHom, monomialHom_right]

end TensorInducedAlgAut

section ChangeTransversal

variable {G : Type v} [Group G] (U : Subgroup G) (s t : U.LeftTransversal)
  (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

/-- The `R`-algebra equivalence comparing tensor induction along two left transversals `s` and `t`.
It acts on `⨂[R] _ : G ⧸ U, A` by the base-group comparison element
`U.monomialChangeTransversal s t`, upgrading `U.tensorInducedChangeTransversalLinearEquiv` to
`AlgEquiv`. -/
noncomputable def tensorInducedChangeTransversalAlgEquiv :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] ⨂[R] _ : G ⧸ U, A :=
  WreathProduct.tensorAlgAut R U A (G ⧸ U) (U.monomialChangeTransversal s t)

/-- The underlying linear equivalence of `tensorInducedChangeTransversalAlgEquiv` is
`tensorInducedChangeTransversalLinearEquiv`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_toLinearEquiv :
    (U.tensorInducedChangeTransversalAlgEquiv s t R A).toLinearEquiv =
      U.tensorInducedChangeTransversalLinearEquiv s t
        (Representation.ofDistribMulAction R U A) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro z
  rw [tensorInducedChangeTransversalAlgEquiv, WreathProduct.tensorAlgAut_toLinearMap]
  exact (U.tensorInducedChangeTransversalLinearEquiv_apply s t
    (Representation.ofDistribMulAction R U A) z).symm

/-- On a pure tensor, `tensorInducedChangeTransversalAlgEquiv` applies the transversal difference
`(U.monomialChangeTransversal s t).left x` in each coset coordinate `x`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_tprod (m : G ⧸ U → A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.monomialChangeTransversal s t).left x • m x := by
  simp [tensorInducedChangeTransversalAlgEquiv, ← Equiv.Perm.inv_def]

/-- `tensorInducedChangeTransversalAlgEquiv` acts in place on `singleAlgHom x a` by the
transversal difference at `x`. -/
@[simp↓]
theorem tensorInducedChangeTransversalAlgEquiv_singleAlgHom [DecidableEq (G ⧸ U)]
    (x : G ⧸ U) (a : A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom x ((U.monomialChangeTransversal s t).left x • a) := by
  rw [tensorInducedChangeTransversalAlgEquiv, WreathProduct.tensorAlgAut_singleAlgHom,
    monomialChangeTransversal_right, Equiv.Perm.one_apply]

/-- Comparing a transversal with itself gives `AlgEquiv.refl`. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_self :
    U.tensorInducedChangeTransversalAlgEquiv s s R A = AlgEquiv.refl := by
  rw [tensorInducedChangeTransversalAlgEquiv, monomialChangeTransversal_self, map_one]
  rfl

/-- Change-of-transversal algebra equivalences compose through an intermediate transversal. -/
theorem tensorInducedChangeTransversalAlgEquiv_trans (v : U.LeftTransversal) :
    (U.tensorInducedChangeTransversalAlgEquiv t v R A).trans
        (U.tensorInducedChangeTransversalAlgEquiv s t R A) =
      U.tensorInducedChangeTransversalAlgEquiv s v R A := by
  apply AlgEquiv.ext
  intro z
  rw [AlgEquiv.trans_apply, tensorInducedChangeTransversalAlgEquiv,
    tensorInducedChangeTransversalAlgEquiv, tensorInducedChangeTransversalAlgEquiv,
    ← AlgEquiv.mul_apply, ← map_mul, monomialChangeTransversal_mul]

/-- Reversing the two transversals gives the inverse algebra equivalence. -/
@[simp]
theorem tensorInducedChangeTransversalAlgEquiv_symm :
    (U.tensorInducedChangeTransversalAlgEquiv s t R A).symm =
      U.tensorInducedChangeTransversalAlgEquiv t s R A := by
  refine AlgEquiv.ext fun z ↦ (U.tensorInducedChangeTransversalAlgEquiv s t R A).injective ?_
  rw [AlgEquiv.apply_symm_apply]
  have h := AlgEquiv.congr_fun (U.tensorInducedChangeTransversalAlgEquiv_trans s t R A s) z
  simpa using h.symm

/-- `tensorInducedChangeTransversalAlgEquiv` intertwines the `G`-algebra actions attached to `t`
and `s`. -/
theorem tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut (g : G)
    (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedChangeTransversalAlgEquiv s t R A (U.tensorInducedAlgAut t R A g z) =
      U.tensorInducedAlgAut s R A g (U.tensorInducedChangeTransversalAlgEquiv s t R A z) := by
  rw [tensorInducedChangeTransversalAlgEquiv, tensorInducedAlgAut_apply, tensorInducedAlgAut_apply,
    ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul,
    monomialChangeTransversal_mul_monomialHom]

end ChangeTransversal

section Transitivity

variable {G : Type v} [Group G] {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Finite (G ⧸ U)] (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]

/-- Flatten an iterated tensor-induced `R`-algebra along a subgroup tower `V ≤ U ≤ G` and relabel
the product index by `G ⧸ V`. This upgrades `Subgroup.tensorInducedTransitivityLinearEquiv` to an
`R`-algebra equivalence. Only `G ⧸ U` must be finite, and `A` need not be commutative. -/
noncomputable def tensorInducedTransitivityAlgEquiv :
    (⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, A) ≃ₐ[R] (⨂[R] _ : G ⧸ V, A) :=
  AlgEquiv.ofLinearEquiv (tensorInducedTransitivityLinearEquiv hVU s)
    (by simp [PiTensorProduct.one_def, Pi.one_def])
    (LinearMap.map_mul_iff _ |>.mpr <| by
      apply PiTensorProduct.ext_sigma_tprod
      intro m
      apply PiTensorProduct.ext_sigma_tprod
      intro n
      simp [PiTensorProduct.tprod_mul_tprod, Pi.mul_def])

/-- The underlying linear equivalence of `tensorInducedTransitivityAlgEquiv` is
`tensorInducedTransitivityLinearEquiv`. -/
@[simp]
theorem tensorInducedTransitivityAlgEquiv_toLinearEquiv :
    (tensorInducedTransitivityAlgEquiv hVU s R A).toLinearEquiv =
      tensorInducedTransitivityLinearEquiv hVU s := (rfl)

/-- On tensors of pure tensors, `tensorInducedTransitivityAlgEquiv` reads off the tower coordinates
of each coset in `G ⧸ V`. -/
@[simp]
theorem tensorInducedTransitivityAlgEquiv_tprod (m : G ⧸ U → U ⧸ V.subgroupOf U → A) :
    tensorInducedTransitivityAlgEquiv hVU s R A
        (PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R fun q : G ⧸ V ↦
        m (quotientEquivProdOfLE' hVU (U.leftTransversalRep s) (U.leftTransversalRep_mk s) q).1
          (quotientEquivProdOfLE' hVU (U.leftTransversalRep s) (U.leftTransversalRep_mk s) q).2 :=
  tensorInducedTransitivityLinearEquiv_tprod hVU s m

/-- The inverse algebra equivalence regroups a pure tensor on `G ⧸ V` into outer and inner pure
tensors along `(G ⧸ U) × (U ⧸ V.subgroupOf U)`. -/
@[simp]
theorem tensorInducedTransitivityAlgEquiv_symm_tprod (m : G ⧸ V → A) :
    (tensorInducedTransitivityAlgEquiv hVU s R A).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R fun b ↦
        m ((quotientEquivProdOfLE' hVU (U.leftTransversalRep s)
          (U.leftTransversalRep_mk s)).symm (a, b)) :=
  tensorInducedTransitivityLinearEquiv_symm_tprod hVU s m

end Transitivity

/-! ### The bundled tensor-induced `G`-algebra `Subgroup.TensorInduced` -/

/-- The tensor-induced carrier `⨂[R] _ : G ⧸ U, A`, bundled with the subgroup `U` and left
transversal `s` in its type so that it carries `MulSemiringAction G` alongside its ring and
`R`-algebra structures. -/
@[ext]
structure TensorInduced {G : Type v} [Group G] (U : Subgroup G) (s : U.LeftTransversal)
    (R : Type u) (A : Type w) [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- Package an element of `⨂[R] _ : G ⧸ U, A` into `U.TensorInduced s R A`. -/
  ofTensor ::
  /-- The underlying tensor in `⨂[R] _ : G ⧸ U, A`. -/
  toTensor : ⨂[R] _ : G ⧸ U, A

namespace TensorInduced

section Module

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommSemiring R] [AddCommMonoid A] [Module R A]

theorem toTensor_injective :
    Function.Injective (toTensor : U.TensorInduced s R A → ⨂[R] _ : G ⧸ U, A) :=
  fun _ _ ↦ TensorInduced.ext

@[simp]
theorem ofTensor_toTensor (z : U.TensorInduced s R A) : ofTensor z.toTensor = z := (rfl)

@[simp]
theorem toTensor_ofTensor (z : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor z : U.TensorInduced s R A).toTensor = z := (rfl)

instance : Zero (U.TensorInduced s R A) := ⟨ofTensor 0⟩
instance : Add (U.TensorInduced s R A) := ⟨fun x y ↦ ofTensor (x.toTensor + y.toTensor)⟩
instance : SMul ℕ (U.TensorInduced s R A) := ⟨fun n x ↦ ofTensor (n • x.toTensor)⟩
instance : SMul R (U.TensorInduced s R A) := ⟨fun r x ↦ ofTensor (r • x.toTensor)⟩

@[simp] theorem toTensor_zero : (0 : U.TensorInduced s R A).toTensor = 0 := (rfl)
@[simp] theorem ofTensor_zero : (ofTensor 0 : U.TensorInduced s R A) = 0 := (rfl)
@[simp] theorem toTensor_add (x y : U.TensorInduced s R A) :
    (x + y).toTensor = x.toTensor + y.toTensor := (rfl)
@[simp] theorem ofTensor_add (x y : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor (x + y) : U.TensorInduced s R A) = ofTensor x + ofTensor y := (rfl)
@[simp] theorem toTensor_nsmul (n : ℕ) (x : U.TensorInduced s R A) :
    (n • x).toTensor = n • x.toTensor := (rfl)
@[simp] theorem toTensor_smul_ring (r : R) (x : U.TensorInduced s R A) :
    (r • x).toTensor = r • x.toTensor := (rfl)

instance : AddCommMonoid (U.TensorInduced s R A) :=
  toTensor_injective.addCommMonoid toTensor rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module R (U.TensorInduced s R A) :=
  toTensor_injective.module R
    { toFun := toTensor, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ ↦ rfl)

variable (U s R A) in
/-- The tautological `R`-linear equivalence between `U.TensorInduced s R A` and its underlying
tensor power `⨂[R] _ : G ⧸ U, A`. -/
def linearEquivTensor : U.TensorInduced s R A ≃ₗ[R] ⨂[R] _ : G ⧸ U, A where
  toFun := toTensor
  invFun := ofTensor
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem linearEquivTensor_apply (z : U.TensorInduced s R A) :
    linearEquivTensor U s R A z = z.toTensor := (rfl)

@[simp]
theorem linearEquivTensor_symm_apply (z : ⨂[R] _ : G ⧸ U, A) :
    (linearEquivTensor U s R A).symm z = ofTensor z := (rfl)

/-- Construct a pure tensor directly in `U.TensorInduced s R A`. -/
def tprod (m : G ⧸ U → A) : U.TensorInduced s R A :=
  ofTensor (PiTensorProduct.tprod R m)

@[simp]
theorem toTensor_tprod (m : G ⧸ U → A) :
    (tprod m : U.TensorInduced s R A).toTensor = PiTensorProduct.tprod R m := (rfl)

end Module

section AddCommGroup

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommRing R] [AddCommGroup A] [Module R A]

instance : Neg (U.TensorInduced s R A) := ⟨fun x ↦ ofTensor (-x.toTensor)⟩
instance : Sub (U.TensorInduced s R A) := ⟨fun x y ↦ ofTensor (x.toTensor - y.toTensor)⟩
instance : SMul ℤ (U.TensorInduced s R A) := ⟨fun n x ↦ ofTensor (n • x.toTensor)⟩

@[simp] theorem toTensor_neg (x : U.TensorInduced s R A) : (-x).toTensor = -x.toTensor := (rfl)
@[simp] theorem ofTensor_neg (x : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor (-x) : U.TensorInduced s R A) = -ofTensor x := (rfl)
@[simp] theorem toTensor_sub (x y : U.TensorInduced s R A) :
    (x - y).toTensor = x.toTensor - y.toTensor := (rfl)
@[simp] theorem ofTensor_sub (x y : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor (x - y) : U.TensorInduced s R A) = ofTensor x - ofTensor y := (rfl)
@[simp] theorem toTensor_zsmul (n : ℤ) (x : U.TensorInduced s R A) :
    (n • x).toTensor = n • x.toTensor := (rfl)

instance : AddCommGroup (U.TensorInduced s R A) :=
  toTensor_injective.addCommGroup toTensor rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end AddCommGroup

section Semiring

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Algebra R A]

noncomputable instance : One (U.TensorInduced s R A) := ⟨ofTensor 1⟩
noncomputable instance : Mul (U.TensorInduced s R A) :=
  ⟨fun x y ↦ ofTensor (x.toTensor * y.toTensor)⟩
noncomputable instance : Pow (U.TensorInduced s R A) ℕ := ⟨fun x n ↦ ofTensor (x.toTensor ^ n)⟩
noncomputable instance : NatCast (U.TensorInduced s R A) := ⟨fun n ↦ ofTensor n⟩

@[simp] theorem toTensor_one : (1 : U.TensorInduced s R A).toTensor = 1 := (rfl)
@[simp] theorem ofTensor_one : (ofTensor 1 : U.TensorInduced s R A) = 1 := (rfl)
@[simp] theorem toTensor_mul (x y : U.TensorInduced s R A) :
    (x * y).toTensor = x.toTensor * y.toTensor := (rfl)
@[simp] theorem ofTensor_mul (x y : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor (x * y) : U.TensorInduced s R A) = ofTensor x * ofTensor y := (rfl)
@[simp] theorem toTensor_pow (x : U.TensorInduced s R A) (n : ℕ) :
    (x ^ n).toTensor = x.toTensor ^ n := (rfl)
@[simp] theorem toTensor_natCast (n : ℕ) :
    ((n : U.TensorInduced s R A)).toTensor = n := (rfl)

@[simp]
theorem tprod_one : (tprod 1 : U.TensorInduced s R A) = 1 := (rfl)

@[simp]
theorem tprod_mul_tprod (m n : G ⧸ U → A) :
    (tprod m : U.TensorInduced s R A) * tprod n = tprod (m * n) :=
  TensorInduced.ext (PiTensorProduct.tprod_mul_tprod m n)

noncomputable instance : Semiring (U.TensorInduced s R A) :=
  toTensor_injective.semiring toTensor rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)

noncomputable instance : Algebra R (U.TensorInduced s R A) :=
  Algebra.ofModule
    (fun r x y ↦ TensorInduced.ext <| smul_mul_assoc r x.toTensor y.toTensor)
    (fun r x y ↦ TensorInduced.ext <| mul_smul_comm r x.toTensor y.toTensor)

@[simp]
theorem toTensor_algebraMap (r : R) :
    (algebraMap R (U.TensorInduced s R A) r).toTensor = algebraMap R (⨂[R] _ : G ⧸ U, A) r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rfl

variable (U s R A) in
/-- The tautological `R`-algebra equivalence between `U.TensorInduced s R A` and its underlying
tensor power `⨂[R] _ : G ⧸ U, A`. -/
noncomputable def algEquivTensor : U.TensorInduced s R A ≃ₐ[R] ⨂[R] _ : G ⧸ U, A :=
  AlgEquiv.ofLinearEquiv (linearEquivTensor U s R A) rfl fun _ _ ↦ rfl

@[simp]
theorem algEquivTensor_apply (z : U.TensorInduced s R A) :
    algEquivTensor U s R A z = z.toTensor := (rfl)

@[simp]
theorem algEquivTensor_symm_apply (z : ⨂[R] _ : G ⧸ U, A) :
    (algEquivTensor U s R A).symm z = ofTensor z := (rfl)

/-- Inclusion of slot `x` as an `R`-algebra homomorphism into `U.TensorInduced s R A`. -/
noncomputable def singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) :
    A →ₐ[R] U.TensorInduced s R A :=
  (algEquivTensor U s R A).symm.toAlgHom.comp
    (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : G ⧸ U ↦ A) x)

@[simp]
theorem toTensor_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    (singleAlgHom x a : U.TensorInduced s R A).toTensor =
      PiTensorProduct.singleAlgHom (R := R) (A := fun _ : G ⧸ U ↦ A) x a := (rfl)

end Semiring

section Ring

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]

noncomputable instance : IntCast (U.TensorInduced s R A) := ⟨fun n ↦ ofTensor n⟩

@[simp] theorem toTensor_intCast (n : ℤ) :
    ((n : U.TensorInduced s R A)).toTensor = n := (rfl)

noncomputable instance : Ring (U.TensorInduced s R A) :=
  toTensor_injective.ring toTensor rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Ring

section CommSemiring

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommSemiring R] [CommSemiring A] [Algebra R A]

noncomputable instance : CommSemiring (U.TensorInduced s R A) :=
  toTensor_injective.commSemiring toTensor rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)

end CommSemiring

section CommRing

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]

noncomputable instance : CommRing (U.TensorInduced s R A) :=
  toTensor_injective.commRing toTensor rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

end CommRing

section Action

variable {G : Type v} [Group G] {U : Subgroup G} {s : U.LeftTransversal}
  {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A]

noncomputable instance : SMul G (U.TensorInduced s R A) :=
  ⟨fun g z ↦ ofTensor (U.tensorInducedAlgAut s R A g z.toTensor)⟩

/-- `toTensor` intertwines the `G`-action on `U.TensorInduced s R A` with
`U.tensorInducedAlgAut s R A`. -/
@[simp]
theorem toTensor_smul_group (g : G) (z : U.TensorInduced s R A) :
    (g • z).toTensor = U.tensorInducedAlgAut s R A g z.toTensor := (rfl)

noncomputable instance : MulSemiringAction G (U.TensorInduced s R A) where
  one_smul z := TensorInduced.ext <| by simp [AlgEquiv.one_apply]
  mul_smul g h z := TensorInduced.ext <| by simp [AlgEquiv.mul_apply]
  smul_zero g := TensorInduced.ext <| map_zero (U.tensorInducedAlgAut s R A g)
  smul_add g x y :=
    TensorInduced.ext <| map_add (U.tensorInducedAlgAut s R A g) x.toTensor y.toTensor
  smul_one g := TensorInduced.ext <| map_one (U.tensorInducedAlgAut s R A g)
  smul_mul g x y :=
    TensorInduced.ext <| map_mul (U.tensorInducedAlgAut s R A g) x.toTensor y.toTensor

instance : SMulCommClass G R (U.TensorInduced s R A) where
  smul_comm g r z := TensorInduced.ext <| map_smul (U.tensorInducedAlgAut s R A g) r z.toTensor

/-- `ofTensor` intertwines `U.tensorInducedAlgAut s R A` with the `G`-action on
`U.TensorInduced s R A`. -/
@[simp]
theorem ofTensor_tensorInducedAlgAut (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    (ofTensor (U.tensorInducedAlgAut s R A g z) : U.TensorInduced s R A) = g • ofTensor z := (rfl)

/-- On a pure tensor, `g` permutes the coset coordinates by `g⁻¹` and acts slotwise by the
transversal word `(U.monomialHom s g).left`. -/
@[simp]
theorem smul_tprod (g : G) (m : G ⧸ U → A) :
    g • (tprod m : U.TensorInduced s R A) =
      tprod fun x ↦ (U.monomialHom s g).left x • m (g⁻¹ • x) :=
  TensorInduced.ext (U.tensorInducedAlgAut_apply_tprod s R A g m)

/-- `g` moves the factor inclusion at coset `x` to coset `g • x` and acts by the transversal word
at `g • x`. -/
@[simp↓]
theorem smul_singleAlgHom [DecidableEq (G ⧸ U)] (g : G) (x : G ⧸ U) (a : A) :
    g • (singleAlgHom x a : U.TensorInduced s R A) =
      singleAlgHom (g • x) ((U.monomialHom s g).left (g • x) • a) :=
  TensorInduced.ext (U.tensorInducedAlgAut_singleAlgHom s R A g x a)

variable (U s R A) in
/-- As a `G`-representation, `U.TensorInduced s R A` is canonically equivalent to
`U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)`. -/
noncomputable def representationEquiv :
    (Representation.ofDistribMulAction R G (U.TensorInduced s R A)).Equiv
      (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A)) :=
  Representation.Equiv.mk (linearEquivTensor U s R A) fun g ↦ LinearMap.ext fun z ↦
    U.tensorInducedAlgAut_apply_eq_tensorInducedRepresentation s R A g z.toTensor

/-- The underlying linear equivalence of `representationEquiv` is `linearEquivTensor`. -/
@[simp]
theorem representationEquiv_toLinearEquiv :
    (representationEquiv U s R A).toLinearEquiv = linearEquivTensor U s R A := (rfl)

/-- `representationEquiv` unwraps `toTensor`. -/
@[simp]
theorem representationEquiv_apply (z : U.TensorInduced s R A) :
    representationEquiv U s R A z = z.toTensor := (rfl)

/-- The inverse of `representationEquiv` wraps a tensor via `ofTensor`. -/
@[simp]
theorem representationEquiv_symm_apply (z : ⨂[R] _ : G ⧸ U, A) :
    (representationEquiv U s R A).symm z = ofTensor z := (rfl)

open CategoryTheory in
variable (U s) in
/-- In `Rep R G`, the underlying representation of `U.TensorInduced s R A` is canonically
isomorphic to `(U.tensorInductionFunctor s).obj (Rep.ofDistribMulAction R U A)`. -/
noncomputable def repIsoTensorInductionFunctor (R : Type u) (A : Type w)
    [CommRing R] [Ring A] [Algebra R A] [MulSemiringAction U A] [SMulCommClass U R A] :
    Rep.ofDistribMulAction R G (U.TensorInduced s R A) ≅
      (U.tensorInductionFunctor (R := R) s).obj (Rep.ofDistribMulAction R U A) :=
  Rep.mkIso <| Representation.Equiv.mk (linearEquivTensor U s R A) fun g ↦
    LinearMap.ext fun z ↦ LinearMap.congr_fun
      (WreathProduct.tensorAlgAut_toLinearMap R A (G ⧸ U) (U.monomialHom s g)) z.toTensor

variable (U s) in
/-- The forward morphism of `repIsoTensorInductionFunctor` unwraps `toTensor`. -/
@[simp]
theorem repIsoTensorInductionFunctor_hom_hom_apply {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] [MulSemiringAction U A] [SMulCommClass U R A]
    (z : U.TensorInduced s R A) :
    (repIsoTensorInductionFunctor U s R A).hom.hom z = z.toTensor := (rfl)

variable (U R A) in
/-- Changing the left transversal from `t` to `s` gives an `R`-algebra equivalence between
`U.TensorInduced t R A` and `U.TensorInduced s R A`. -/
noncomputable def changeTransversalAlgEquiv (s t : U.LeftTransversal) :
    U.TensorInduced t R A ≃ₐ[R] U.TensorInduced s R A :=
  (algEquivTensor U t R A).trans
    ((U.tensorInducedChangeTransversalAlgEquiv s t R A).trans (algEquivTensor U s R A).symm)

/-- `toTensor` carries `changeTransversalAlgEquiv` to `U.tensorInducedChangeTransversalAlgEquiv`. -/
@[simp]
theorem toTensor_changeTransversalAlgEquiv (s t : U.LeftTransversal)
    (z : U.TensorInduced t R A) :
    (changeTransversalAlgEquiv U R A s t z).toTensor =
      U.tensorInducedChangeTransversalAlgEquiv s t R A z.toTensor := (rfl)

/-- On a pure tensor, `changeTransversalAlgEquiv` acts slotwise by the transversal difference. -/
@[simp]
theorem changeTransversalAlgEquiv_tprod (s t : U.LeftTransversal) (m : G ⧸ U → A) :
    changeTransversalAlgEquiv U R A s t (tprod m) =
      tprod fun x ↦ (U.monomialChangeTransversal s t).left x • m x :=
  TensorInduced.ext (U.tensorInducedChangeTransversalAlgEquiv_tprod s t R A m)

/-- `changeTransversalAlgEquiv` is `G`-equivariant. -/
@[simp]
theorem changeTransversalAlgEquiv_smul (s t : U.LeftTransversal) (g : G)
    (z : U.TensorInduced t R A) :
    changeTransversalAlgEquiv U R A s t (g • z) =
      g • changeTransversalAlgEquiv U R A s t z :=
  TensorInduced.ext <|
    U.tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut s t R A g z.toTensor

variable (U R A) in
/-- Changing the left transversal from `t` to `s` as a homomorphism of `G`-semirings. -/
noncomputable def changeTransversalMulSemiringActionHom (s t : U.LeftTransversal) :
    U.TensorInduced t R A →+*[G] U.TensorInduced s R A where
  __ := (changeTransversalAlgEquiv U R A s t).toRingHom
  map_smul' := changeTransversalAlgEquiv_smul s t

/-- Evaluating `changeTransversalMulSemiringActionHom` gives `changeTransversalAlgEquiv`. -/
@[simp]
theorem changeTransversalMulSemiringActionHom_apply (s t : U.LeftTransversal)
    (z : U.TensorInduced t R A) :
    changeTransversalMulSemiringActionHom U R A s t z =
      changeTransversalAlgEquiv U R A s t z := (rfl)

end Action

end TensorInduced

end Subgroup
