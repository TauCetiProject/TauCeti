/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.GroupTheory.GroupAction.Hom
public import TauCeti.RingTheory.PiTensorProduct.Map
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Tensor-induced `G`-algebras and Evens' twisted multiplication

When a group `D` acts on an `R`-algebra `A` by `R`-algebra automorphisms, the permutation wreath
product `WreathProduct D ι` acts on the indexed tensor power `⨂[R] _ : ι, A` by `R`-algebra
automorphisms: the top permutation reindexes the tensor factors via
`PiTensorProduct.reindexAlgEquiv` and the base coordinates act slotwise via
`PiTensorProduct.congrAlgEquiv`. Pulling this action back along `Subgroup.monomialHom s` for a
subgroup `U ≤ G` and a left transversal `s : U.LeftTransversal` makes the coset-indexed tensor
power `⨂[R] _ : G ⧸ U, A` a `G`-algebra, bundled as `Subgroup.TensorInduced U s R A`.

When `A` is a commutative `G`-algebra over `R` and `G ⧸ U` is finite, Evens' twisted
multiplication
```text
⨂[R] _ : G ⧸ U, A ⟶ A,     ⨂ₜ x, a x ↦ ∏ x : G ⧸ U, r_s(x) • a x
```
is a `G`-equivariant `R`-algebra homomorphism (`Subgroup.tensorInducedMulAlgHom`, bundled as a
`G`-semiring homomorphism `Subgroup.TensorInduced.mulSemiringActionHom`), independent of the chosen
left transversal up to `Subgroup.tensorInducedChangeTransversalAlgEquiv`, and transitive along
subgroup towers `V ≤ U ≤ G`.

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
  `Semiring`, `Ring`, `CommSemiring`, `CommRing`, `Algebra R`, and `MulSemiringAction G` instances.
* `Subgroup.tensorInducedMulAlgHom`, `Subgroup.TensorInduced.mulSemiringActionHom`: Evens'
  twisted multiplication `⨂ₜ x, a x ↦ ∏ x, r_s(x) • a x` as an `R`-algebra homomorphism and as a
  homomorphism of `G`-semirings `U.TensorInduced s R A →+*[G] A`.

## Main results

* `Subgroup.tensorInducedChangeTransversalAlgEquiv_tensorInducedAlgAut`: changing the transversal
  intertwines the tensor-induced `G`-algebra actions.
* `Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut`: `G`-equivariance of Evens' twisted
  multiplication.
* `Subgroup.tensorInducedMulAlgHom_changeTransversal`,
  `Subgroup.tensorInducedMulAlgHom_comp_changeTransversal`: independence of the chosen transversal.
* `Subgroup.tensorInducedMulAlgHom_transitivity`: compatibility of Evens' twisted multiplication
  with transitivity along `V ≤ U ≤ G`.
* `Subgroup.tensorInducedMulAlgHom_of_smul_eq_self`,
  `Subgroup.tensorInducedMulAlgHom_tprod_const_of_smul_eq`: specialization to trivial `G`-actions
  and `G`-fixed elements.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society **108** (1963), §§2–6, pp. 56–62.
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

/-! ### Evens' twisted multiplication on a tensor-induced commutative `G`-algebra -/

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
    mulAlgHom U s R A z = U.tensorInducedMulAlgHom s R A z.toTensor := (rfl)

/-- On `ofTensor z`, `TensorInduced.mulAlgHom` evaluates `Subgroup.tensorInducedMulAlgHom` on
`z`. -/
@[simp]
theorem mulAlgHom_ofTensor (z : ⨂[R] _ : G ⧸ U, A) :
    mulAlgHom U s R A (ofTensor z) = U.tensorInducedMulAlgHom s R A z := (rfl)

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

/-- The involution of `ℤ[X]` sending `X` to `-X`. -/
private noncomputable def polyNegXEquiv : Polynomial ℤ ≃ₐ[ℤ] Polynomial ℤ :=
  AlgEquiv.ofAlgHom (aeval (-X : Polynomial ℤ)) (aeval (-X : Polynomial ℤ))
    (Polynomial.algHom_ext <| by simp)
    (Polynomial.algHom_ext <| by simp)

private theorem polyNegXEquiv_sq : polyNegXEquiv ^ 2 = 1 := by
  rw [sq]
  exact AlgEquiv.ext fun p ↦ DFunLike.congr_fun
    (Polynomial.algHom_ext (f := (aeval (-X : Polynomial ℤ)).comp (aeval (-X)))
      (g := AlgHom.id ℤ (Polynomial ℤ)) (by simp)) p

/-- Group homomorphism `Multiplicative (ZMod 2) →* (ℤ[X] ≃ₐ[ℤ] ℤ[X])` acting by `X ↦ -X`. -/
private noncomputable def polyNegXAut :
    Multiplicative (ZMod 2) →* (Polynomial ℤ ≃ₐ[ℤ] Polynomial ℤ) where
  toFun g := polyNegXEquiv ^ g.toAdd.val
  map_one' := rfl
  map_mul' g h := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    nth_rw 2 [← Nat.div_add_mod (g.toAdd.val + h.toAdd.val) 2]
    rw [pow_add, pow_mul, polyNegXEquiv_sq, one_pow, one_mul]

private theorem polyNegXAut_apply (g : Multiplicative (ZMod 2)) :
    polyNegXAut g = polyNegXEquiv ^ g.toAdd.val :=
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
    rfl
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
