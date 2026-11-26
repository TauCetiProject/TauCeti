/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.RepresentationTheory.Tensor.Induction.Ring.Basic

/-!
# Untwisting, naturality, and evaluations of the tensor-induced algebra multiplication

`TauCeti.RepresentationTheory.Tensor.Induction.Ring.Basic` equips the tensor-induced module
`⨂[R] _ : G ⧸ U, A` of a `U`-algebra `A` with its `G`-action by `R`-algebra automorphisms
(`Subgroup.tensorInducedAlgAut`), the change-of-transversal algebra isomorphism
(`Subgroup.tensorInducedChangeTransversalAlgEquiv`), and Evens' transversal multiplication
(`Subgroup.tensorInducedMulAlgHom`),

```text
⨂ₜ x, a x ↦ ∏ x : G ⧸ U, r_s(x) • a x.
```

This file develops that multiplication further. When `A` carries an action of the ambient group
`G` by `R`-algebra automorphisms, applying the chosen coset representatives slotwise gives an
untwisting `R`-algebra equivalence `Subgroup.tensorInducedUntwistAlgEquiv` on
`⨂[R] _ : G ⧸ U, A`. It conjugates the monomial `G`-action into the transversal-free action that
permutes coset slots and applies `g` in every factor, and it factors transversal multiplication
through ordinary factor multiplication `PiTensorProduct.mulAlgHom`. Transversal multiplication is
also natural under group homomorphisms that induce bijections of coset spaces, and it is evaluated
on diagonal invariant tensors, over a single coset, and at index two. Specializing `R = ℤ` yields
the tensor-induced ring and `G`-ring multiplication of a commutative `G`-ring.

## Main definitions

* `Subgroup.tensorInducedUntwistAlgEquiv`: the slotwise untwisting `R`-algebra equivalence
  `⨂ₜ x, a x ↦ ⨂ₜ x, r_s(x) • a x` for an ambient `G`-algebra `A`.
* `Subgroup.tensorInducedMulSubsingletonAlgEquiv`: the `R`-algebra equivalence
  `(⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A` obtained when `G ⧸ U` is a subsingleton (for instance `U = ⊤`).

## Main results

* `Subgroup.tensorInducedUntwistAlgEquiv_tensorInducedAlgAut`: untwisting identifies the monomial
  `G`-action with coset permutation followed by the diagonal `G`-action.
* `Subgroup.mulAlgHom_tensorInducedUntwistAlgEquiv`: transversal multiplication is untwisting
  followed by `PiTensorProduct.mulAlgHom`.
* `Subgroup.tensorInducedMulAlgHom_reindexAlgEquiv`,
  `Subgroup.tensorInducedMulAlgHom_tensorInducedMapEquiv`: transversal multiplication commutes with
  reindexing and `Subgroup.tensorInducedMapEquiv` along a group homomorphism inducing a bijection of
  coset spaces.
* `Subgroup.tensorInducedMulAlgHom_tensorInducedDiagonal`,
  `Subgroup.tensorInducedMulAlgHom_tprod_of_index_two`: evaluation on diagonal `U`-invariant tensors
  and at index two.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 2--5, p. 60.
-/

public section

open scoped TensorProduct

universe u v v' w w' x

namespace Subgroup

open TauCeti

/-! ### Multiplicativity and change of transversal on underlying representations -/

section TensorInducedAlgebra

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction U A] [SMulCommClass U R A] (s t : U.LeftTransversal)

/-- The tensor-induced representation of a `U`-algebra fixes the multiplicative unit
`1 = ⨂ₜ _, 1`. -/
@[simp]
theorem tensorInducedRepresentation_ofDistribMulAction_one (g : G) :
    U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g 1 = 1 := by
  rw [← U.tensorInducedAlgAut_toLinearMap R A s g, AlgEquiv.toLinearMap_apply, map_one]

/-- The tensor-induced representation of a `U`-algebra distributes over multiplication in
`⨂[R] _ : G ⧸ U, A`. -/
theorem tensorInducedRepresentation_ofDistribMulAction_mul (g : G) (y z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g (y * z) =
      U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g y *
        U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z := by
  rw [← U.tensorInducedAlgAut_toLinearMap R A s g, AlgEquiv.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, map_mul]

/-- Pointwise agreement of `Subgroup.tensorInducedChangeTransversalAlgEquiv` with
`Subgroup.tensorInducedChangeTransversal`. -/
theorem tensorInducedChangeTransversalAlgEquiv_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedChangeTransversalAlgEquiv R A s t z =
      U.tensorInducedChangeTransversal s t (Representation.ofDistribMulAction R U A) z := by
  rw [tensorInducedChangeTransversal_apply,
    ← tensorInducedChangeTransversalAlgEquiv_toLinearEquiv, AlgEquiv.coe_toLinearEquiv]

end TensorInducedAlgebra


/-! ### Untwisting when `A` is an ambient `G`-algebra -/

section Untwist

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [Semiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] (s t : U.LeftTransversal)

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
    U.tensorInducedUntwistAlgEquiv R A s (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ U.leftTransversalRep s x • m x :=
  PiTensorProduct.congrAlgEquiv_tprod _ m

/-- The inverse untwisting acts in coset slot `x` of a pure tensor by
`(U.leftTransversalRep s x)⁻¹`. -/
@[simp]
theorem tensorInducedUntwistAlgEquiv_symm_tprod (m : G ⧸ U → A) :
    (U.tensorInducedUntwistAlgEquiv R A s).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ (U.leftTransversalRep s x)⁻¹ • m x := by
  apply (U.tensorInducedUntwistAlgEquiv R A s).injective
  simp [smul_inv_smul]

/-- Untwisting sends `a` in coset slot `x` to `U.leftTransversalRep s x • a` in slot `x`. -/
@[simp↓]
theorem tensorInducedUntwistAlgEquiv_singleAlgHom [DecidableEq (G ⧸ U)] (x : G ⧸ U) (a : A) :
    U.tensorInducedUntwistAlgEquiv R A s (PiTensorProduct.singleAlgHom x a) =
      PiTensorProduct.singleAlgHom x (U.leftTransversalRep s x • a) := by
  rw [tensorInducedUntwistAlgEquiv, PiTensorProduct.congrAlgEquiv_singleAlgHom,
    MulSemiringAction.toAlgEquiv_apply]

/-- Untwisting absorbs the change-of-transversal algebra equivalence: applying the comparison from
`t` to `s` and then untwisting by `s` is untwisting by `t`. -/
@[simp]
theorem tensorInducedUntwistAlgEquiv_changeTransversalAlgEquiv (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedUntwistAlgEquiv R A s
        (U.tensorInducedChangeTransversalAlgEquiv R A s t z) =
      U.tensorInducedUntwistAlgEquiv R A t z := by
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
    (U.tensorInducedChangeTransversalAlgEquiv R A s t).trans
        (U.tensorInducedUntwistAlgEquiv R A s) =
      U.tensorInducedUntwistAlgEquiv R A t :=
  AlgEquiv.ext (U.tensorInducedUntwistAlgEquiv_changeTransversalAlgEquiv R A s t)

/-- **Untwisting removes the transversal from the `G`-algebra action**:
`tensorInducedUntwistAlgEquiv` intertwines `Subgroup.tensorInducedAlgAut` with the canonical
transversal-free action on `⨂[R] _ : G ⧸ U, A` that permutes coset factors by `g` and acts by `g`
in every factor. -/
theorem tensorInducedUntwistAlgEquiv_tensorInducedAlgAut (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedUntwistAlgEquiv R A s (U.tensorInducedAlgAut R A s g z) =
      PiTensorProduct.congrAlgEquiv (fun _ : G ⧸ U ↦ MulSemiringAction.toAlgEquiv R A g)
        (PiTensorProduct.permAlgEquiv A (MulAction.toPerm g)
          (U.tensorInducedUntwistAlgEquiv R A s z)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, tensorInducedAlgAut_tprod, tensorInducedUntwistAlgEquiv_tprod,
      PiTensorProduct.permAlgEquiv_tprod, PiTensorProduct.congrAlgEquiv_tprod,
      MulSemiringAction.toAlgEquiv_apply, Function.comp_def]
    congr 2
    funext x
    rw [Subgroup.smul_def, monomialHom_left, ← mul_smul, transversal_mul_lWord, mul_smul,
      MulAction.toPerm_symm_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

end Untwist

/-! ### Equivariant multiplication along a transversal -/

section Multiplication

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] (s t : U.LeftTransversal) [Fintype (G ⧸ U)]

/-- Transversal multiplication factors as slotwise untwisting followed by ordinary factor
multiplication `PiTensorProduct.mulAlgHom`. -/
theorem mulAlgHom_tensorInducedUntwistAlgEquiv (z : ⨂[R] _ : G ⧸ U, A) :
    PiTensorProduct.mulAlgHom (U.tensorInducedUntwistAlgEquiv R A s z) =
      U.tensorInducedMulAlgHom R A s z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- As `R`-algebra homomorphisms, `PiTensorProduct.mulAlgHom` composed with
`Subgroup.tensorInducedUntwistAlgEquiv` is `Subgroup.tensorInducedMulAlgHom`. -/
theorem mulAlgHom_comp_tensorInducedUntwistAlgEquiv :
    (PiTensorProduct.mulAlgHom (R := R) (σ := G ⧸ U) (B := A)).comp
        (U.tensorInducedUntwistAlgEquiv R A s).toAlgHom =
      U.tensorInducedMulAlgHom R A s :=
  AlgHom.ext (U.mulAlgHom_tensorInducedUntwistAlgEquiv R A s)

/-- Equivariance of `Subgroup.tensorInducedMulAlgHom`, phrased directly in terms of
`Subgroup.tensorInducedRepresentation`. -/
@[simp]
theorem tensorInducedMulAlgHom_tensorInducedRepresentation (g : G) (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom R A s
        (U.tensorInducedRepresentation s (Representation.ofDistribMulAction R U A) g z) =
      g • U.tensorInducedMulAlgHom R A s z := by
  rw [← U.tensorInducedAlgAut_toLinearMap R A s g, AlgEquiv.toLinearMap_apply,
    tensorInducedMulAlgHom_tensorInducedAlgAut]

/-- Independence of transversal for `Subgroup.tensorInducedMulAlgHom`, phrased with the
representation equivalence `Subgroup.tensorInducedChangeTransversal`. -/
@[simp]
theorem tensorInducedMulAlgHom_changeTransversal (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulAlgHom R A s
        (U.tensorInducedChangeTransversal s t (Representation.ofDistribMulAction R U A) z) =
      U.tensorInducedMulAlgHom R A t z := by
  rw [← tensorInducedChangeTransversalAlgEquiv_apply,
    tensorInducedMulAlgHom_changeTransversalAlgEquiv]

/-- On a `G`-invariant element `a`, transversal multiplication sends the constant pure tensor
`⨂ₜ _, a` to `a ^ |G ⧸ U|`. -/
theorem tensorInducedMulAlgHom_tprod_const_of_smul_eq_self
    (a : A) (ha : ∀ g : G, g • a = a) :
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R fun _ : G ⧸ U ↦ a) =
      a ^ Fintype.card (G ⧸ U) := by
  rw [tensorInducedMulAlgHom_tprod]
  simp [ha]

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
    U'.tensorInducedMulAlgHom R A' (s.map φ e he)
        (PiTensorProduct.map (fun _ : G' ⧸ U' ↦ f.toLinearMap)
          (PiTensorProduct.reindexAlgEquiv (fun _ : G ⧸ U ↦ A) e z)) =
      f (U.tensorInducedMulAlgHom R A s z) := by
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
    U'.tensorInducedMulAlgHom R A' (s.map φ e he)
        (PiTensorProduct.reindexAlgEquiv (fun _ : G ⧸ U ↦ A') e z) =
      U.tensorInducedMulAlgHom R A' s z := by
  simpa only [AlgHom.toLinearMap_id, PiTensorProduct.map_id, LinearMap.id_apply, AlgHom.id_apply]
    using tensorInducedMulAlgHom_map_reindexAlgEquiv (R := R) (U := U) (U' := U') (A := A')
      (A' := A') s φ e he (AlgHom.id R A') hφ z

/-- `Subgroup.tensorInducedMapEquiv` intertwines transversal multiplication along `s` and
`s.map φ e he` whenever the `G`-action on `A'` agrees with pullback along `φ`. -/
theorem tensorInducedMulAlgHom_tensorInducedMapEquiv
    [MulSemiringAction G A'] [SMulCommClass G R A']
    (s : U.LeftTransversal) (φ : G →* G') (ψ : U →* U') (hψ : ∀ u, (ψ u : G') = φ u)
    (e : G ⧸ U ≃ G' ⧸ U') (he : ∀ g : G, e g = (φ g : G' ⧸ U'))
    (ρ : Representation R U' A') (hφ : ∀ (g : G) (a : A'), g • a = φ g • a)
    (z : ⨂[R] _ : G ⧸ U, A') :
    U'.tensorInducedMulAlgHom R A' (s.map φ e he)
        (tensorInducedMapEquiv φ ψ hψ e he s ρ z) =
      U.tensorInducedMulAlgHom R A' s z := by
  rw [← tensorInducedMulAlgHom_reindexAlgEquiv s φ e he hφ z]
  congr 1
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- `Subgroup.tensorInducedMapEquiv.symm` intertwines transversal multiplication along
`s.map φ e he` and `s` whenever the `G`-action on `A'` agrees with pullback along `φ`. -/
theorem tensorInducedMulAlgHom_tensorInducedMapEquiv_symm
    [MulSemiringAction G A'] [SMulCommClass G R A']
    (s : U.LeftTransversal) (φ : G →* G') (ψ : U →* U') (hψ : ∀ u, (ψ u : G') = φ u)
    (e : G ⧸ U ≃ G' ⧸ U') (he : ∀ g : G, e g = (φ g : G' ⧸ U'))
    (ρ : Representation R U' A') (hφ : ∀ (g : G) (a : A'), g • a = φ g • a)
    (z : ⨂[R] _ : G' ⧸ U', A') :
    U.tensorInducedMulAlgHom R A' s
        ((tensorInducedMapEquiv φ ψ hψ e he s ρ).symm z) =
      U'.tensorInducedMulAlgHom R A' (s.map φ e he) z := by
  simpa only [Representation.Equiv.apply_symm_apply] using
    (tensorInducedMulAlgHom_tensorInducedMapEquiv s φ ψ hψ e he ρ hφ
      ((tensorInducedMapEquiv φ ψ hψ e he s ρ).symm z)).symm

end Naturality

/-! ### Diagonal invariant tensors, index one, and index two -/

section Diagonal

variable {R : Type u} [CommRing R] {G : Type v} [Group G] (U : Subgroup G)
variable (A : Type w) [CommRing A] [Algebra R A] [MulSemiringAction G A] [SMulCommClass G R A]
  (s : U.LeftTransversal) [Fintype (G ⧸ U)]

/-- On the diagonal invariant tensor `Representation.tensorInducedDiagonal` of a `U`-invariant
element `a ∈ A`, transversal multiplication evaluates to the multiplicative norm
`∏ x : G ⧸ U, r_s(x) • a`. -/
theorem tensorInducedMulAlgHom_tensorInducedDiagonal
    (a : (Representation.ofDistribMulAction R U A).invariants) :
    U.tensorInducedMulAlgHom R A s
        ((Representation.ofDistribMulAction R U A).tensorInducedDiagonal s a) =
      ∏ x : G ⧸ U, U.leftTransversalRep s x • (a : A) := by
  simp [Representation.coe_tensorInducedDiagonal]

end Diagonal

section Subsingleton

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] (s : U.LeftTransversal) [Fintype (G ⧸ U)]
  [Subsingleton (G ⧸ U)]

/-- **One-coset algebra isomorphism**: when `G ⧸ U` is a subsingleton (for instance `U = ⊤`),
transversal multiplication is an `R`-algebra equivalence `(⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A`. -/
noncomputable def tensorInducedMulSubsingletonAlgEquiv :
    (⨂[R] _ : G ⧸ U, A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (U.tensorInducedMulAlgHom R A s)
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
    (U.tensorInducedMulSubsingletonAlgEquiv R A s).toAlgHom =
      U.tensorInducedMulAlgHom R A s :=
  (rfl)

/-- Applying `Subgroup.tensorInducedMulSubsingletonAlgEquiv` evaluates
`Subgroup.tensorInducedMulAlgHom`. -/
@[simp]
theorem tensorInducedMulSubsingletonAlgEquiv_apply (z : ⨂[R] _ : G ⧸ U, A) :
    U.tensorInducedMulSubsingletonAlgEquiv R A s z =
      U.tensorInducedMulAlgHom R A s z :=
  (rfl)

/-- When `G ⧸ U` has one coset, transversal multiplication on a pure tensor acts on the entry at
`⟦1⟧` by its chosen transversal representative. -/
theorem tensorInducedMulAlgHom_tprod_of_subsingleton (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R m) =
      U.leftTransversalRep s (QuotientGroup.mk 1) • m (QuotientGroup.mk 1) := by
  rw [tensorInducedMulAlgHom_tprod]
  exact Finset.prod_eq_single (QuotientGroup.mk 1)
    (fun x _ hx ↦ absurd (Subsingleton.elim x _) hx) (by simp)

/-- The inverse of `Subgroup.tensorInducedMulSubsingletonAlgEquiv` sends `a` to the pure tensor
whose coordinate at `x` is `(r_s x)⁻¹ • a`. -/
@[simp]
theorem tensorInducedMulSubsingletonAlgEquiv_symm_apply (a : A) :
    (U.tensorInducedMulSubsingletonAlgEquiv R A s).symm a =
      PiTensorProduct.tprod R fun x ↦ (U.leftTransversalRep s x)⁻¹ • a := by
  rw [AlgEquiv.symm_apply_eq, tensorInducedMulSubsingletonAlgEquiv_apply,
    tensorInducedMulAlgHom_tprod_of_subsingleton, smul_inv_smul]

end Subsingleton

section IndexTwo

variable {G : Type v} [Group G] (U : Subgroup G)
variable (R : Type u) (A : Type w) [CommSemiring R] [CommSemiring A] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A] [Fintype (G ⧸ U)]

/-- For a subgroup `U` of index two and `g ∉ U`, transversal multiplication on a pure tensor is
the product of the two coset terms at `⟦1⟧` and `⟦g⟧`. -/
theorem tensorInducedMulAlgHom_tprod_of_index_two (s : U.LeftTransversal)
    (hU : U.index = 2) {g : G} (hg : g ∉ U) (m : G ⧸ U → A) :
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R m) =
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
    U.tensorInducedMulAlgHom R A s (PiTensorProduct.tprod R m) =
      m (QuotientGroup.mk 1) * g • m (QuotientGroup.mk g) := by
  rw [tensorInducedMulAlgHom_tprod_of_index_two U R A s hU hg m, h1, one_smul, hg']

end IndexTwo

end Subgroup

/-! ### Concrete checks -/

section Examples

open Polynomial

private abbrev TwoGroup := Multiplicative (ZMod 2)

private def twoGroupGen : TwoGroup := Multiplicative.ofAdd 1

private theorem bot_index_twoGroup : (⊥ : Subgroup TwoGroup).index = 2 :=
  (Subgroup.index_bot (G := TwoGroup)).trans (Nat.card_zmod 2)

private theorem twoGroupGen_notMem_bot : twoGroupGen ∉ (⊥ : Subgroup TwoGroup) := by
  rw [Subgroup.mem_bot]; decide

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
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom R A twoGroupBotTransversal
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
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ twoGroupBotTransversal
        (PiTensorProduct.tprod ℤ v₂₃) = 6 ∧
      (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ twoGroupBotTransversal
        (PiTensorProduct.permAlgEquiv ℤ swap (PiTensorProduct.tprod ℤ v₂₃)) = 6 := by
  let _ : MulSemiringAction TwoGroup ℤ :=
    MulSemiringAction.compHom ℤ (1 : TwoGroup →* (ℤ →+* ℤ))
  intro v₂₃ swap
  have hne : (QuotientGroup.mk twoGroupGen : TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) ≠
      QuotientGroup.mk 1 := TauCeti.mk_ne_mk_one_of_notMem twoGroupGen_notMem_bot
  have hsmul : ∀ (g : TwoGroup) (n : ℤ), g • n = n := fun _ _ ↦ rfl
  refine ⟨?_, ?_⟩
  · rw [twoGroupBotTransversal_tprod, hsmul]; dsimp only [v₂₃]
    simp only [hne, ↓reduceIte]; norm_num
  · rw [PiTensorProduct.permAlgEquiv_tprod, twoGroupBotTransversal_tprod, hsmul]
    dsimp only [v₂₃, swap, Function.comp_def]
    rw [Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp only [hne, ↓reduceIte]; norm_num

/-- Check 2: for one coset (`U = ⊤`) with chosen representative `1`, transversal multiplication
sends `a` to `a` and `1` to `1`. -/
example {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A] (a : A) :
    letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    letI : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofSubsingleton (QuotientGroup.mk 1)
    let s : (⊤ : Subgroup G).LeftTransversal :=
      ⟨Set.range fun _ : G ⧸ (⊤ : Subgroup G) ↦ (1 : G),
        Subgroup.isComplement_range_left fun x ↦ Subsingleton.elim _ x⟩
    (⊤ : Subgroup G).tensorInducedMulAlgHom ℤ A s
        (PiTensorProduct.tprod ℤ fun _ ↦ a) = a ∧
      (⊤ : Subgroup G).tensorInducedMulAlgHom ℤ A s 1 = 1 := by
  let _ : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  let _ : Fintype (G ⧸ (⊤ : Subgroup G)) := Fintype.ofSubsingleton (QuotientGroup.mk 1)
  intro s
  have hs : (⊤ : Subgroup G).leftTransversalRep s (QuotientGroup.mk 1) = 1 :=
    congrFun ((⊤ : Subgroup G).leftTransversalRep_range
      (fun _ : G ⧸ (⊤ : Subgroup G) ↦ (1 : G)) (fun x ↦ Subsingleton.elim _ x))
      (QuotientGroup.mk 1)
  refine ⟨?_, map_one _⟩
  rw [(⊤ : Subgroup G).tensorInducedMulAlgHom_tprod_of_subsingleton, hs, one_smul]

private noncomputable def negXAlgEquiv : ℤ[X] ≃ₐ[ℤ] ℤ[X] :=
  AlgEquiv.ofAlgHom (aeval (-X : ℤ[X])) (aeval (-X : ℤ[X]))
    (Polynomial.algHom_ext <| by simp) (Polynomial.algHom_ext <| by simp)

private noncomputable def twoGroupPolyAct : TwoGroup →* (ℤ[X] →+* ℤ[X]) where
  toFun g := if g.toAdd = 0 then RingHom.id ℤ[X] else negXAlgEquiv.toAlgHom.toRingHom
  map_one' := rfl
  map_mul' g h := by
    by_cases hg : g.toAdd = 0
    · simp [toAdd_mul, hg, ← RingHom.one_def]
    · by_cases hh : h.toAdd = 0
      · simp [toAdd_mul, hh, ← RingHom.one_def]
      · have hgh : (g * h).toAdd = 0 := by revert hg hh g h; decide
        simp only [hgh, hg, hh, ↓reduceIte]
        refine RingHom.ext fun p ↦ ?_
        -- Multiplication in `ℤ[X] →+* ℤ[X]` is composition of ring homomorphisms.
        change RingHom.id ℤ[X] p = negXAlgEquiv (negXAlgEquiv p)
        exact (negXAlgEquiv.symm_apply_apply p).symm

open Classical in
/-- Check 3: on `A = ℤ[X]` with `C₂` acting by `X ↦ -X` and `U = ⊥`, multiplication along
`{1, σ}` sends `X ⊗ 1` to `X`, `1 ⊗ X` to `-X`, and the `C₂`-invariant tensor `X² ⊗ X²` to
`(X²) ^ 2`, and swapping the two tensor factors agrees with acting by `σ` on `ℤ[X]`. -/
example :
    letI : MulSemiringAction TwoGroup ℤ[X] := MulSemiringAction.compHom ℤ[X] twoGroupPolyAct
    let xLeft : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X] :=
      PiTensorProduct.tprod ℤ fun x ↦ if x = QuotientGroup.mk 1 then X else 1
    let xRight : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X] :=
      PiTensorProduct.tprod ℤ fun x ↦ if x = QuotientGroup.mk 1 then 1 else X
    let swap : Equiv.Perm (TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) :=
      Equiv.swap (QuotientGroup.mk 1) (QuotientGroup.mk twoGroupGen)
    (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ[X] twoGroupBotTransversal xLeft = X ∧
      (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ[X] twoGroupBotTransversal
          xRight = -X ∧
      (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ[X] twoGroupBotTransversal
          (PiTensorProduct.tprod ℤ fun _ ↦ X ^ 2) = (X ^ 2) ^ 2 ∧
      ∀ z : ⨂[ℤ] _ : TwoGroup ⧸ (⊥ : Subgroup TwoGroup), ℤ[X],
        (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ[X] twoGroupBotTransversal
            (PiTensorProduct.permAlgEquiv ℤ[X] swap z) =
          twoGroupGen •
            (⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom ℤ ℤ[X]
              twoGroupBotTransversal z := by
  let _ : MulSemiringAction TwoGroup ℤ[X] := MulSemiringAction.compHom ℤ[X] twoGroupPolyAct
  intro xLeft xRight swap
  have hne : (QuotientGroup.mk twoGroupGen : TwoGroup ⧸ (⊥ : Subgroup TwoGroup)) ≠
      QuotientGroup.mk 1 := TauCeti.mk_ne_mk_one_of_notMem twoGroupGen_notMem_bot
  have hσX : twoGroupGen • (X : ℤ[X]) = -X := by
    -- Unfold the action through `MulSemiringAction.compHom` to evaluate `twoGroupPolyAct`.
    change twoGroupPolyAct twoGroupGen X = -X
    simp [twoGroupPolyAct, twoGroupGen, negXAlgEquiv]
  have hσ1 : twoGroupGen • (1 : ℤ[X]) = 1 := smul_one twoGroupGen
  have hinvX2 : ∀ g : TwoGroup, g • (X ^ 2 : ℤ[X]) = X ^ 2 := fun g ↦ by
    -- Unfold `•` through `MulSemiringAction.compHom` to check both cases of `twoGroupPolyAct`.
    change twoGroupPolyAct g (X ^ 2) = X ^ 2
    by_cases hg : g = 1 <;> simp [twoGroupPolyAct, hg, negXAlgEquiv]
  refine ⟨?_, ?_, ?_, fun z ↦ ?_⟩
  · dsimp only [xLeft]; rw [twoGroupBotTransversal_tprod]
    simp only [hne, ↓reduceIte, hσ1, mul_one]
  · dsimp only [xRight]; rw [twoGroupBotTransversal_tprod]
    simp only [hne, ↓reduceIte, hσX, one_mul]
  · rw [(⊥ : Subgroup TwoGroup).tensorInducedMulAlgHom_tprod_const_of_smul_eq_self
      ℤ ℤ[X] twoGroupBotTransversal (X ^ 2) hinvX2,
      Fintype.card_eq_nat_card, ← Subgroup.index_eq_card, bot_index_twoGroup]
  · -- For `U = ⊥`, every transversal word lies in `⊥` and is `1`, while `σ` swaps the cosets.
    have hinv := mt (⊥ : Subgroup TwoGroup).inv_mem_iff.1 twoGroupGen_notMem_bot
    have hperm : PiTensorProduct.permAlgEquiv (R := ℤ) ℤ[X] swap z =
        (⊥ : Subgroup TwoGroup).tensorInducedAlgAut
          ℤ ℤ[X] twoGroupBotTransversal twoGroupGen z := by
      induction z using PiTensorProduct.induction_on with
      | smul_tprod r m =>
        simp only [map_smul, PiTensorProduct.permAlgEquiv_tprod, Subgroup.tensorInducedAlgAut_tprod,
          Function.comp_def]
        dsimp only [swap]
        rw [Equiv.symm_swap]
        congr 2; funext x
        have hu :
            ((⊥ : Subgroup TwoGroup).monomialHom twoGroupBotTransversal twoGroupGen).left x = 1 :=
          Subsingleton.elim _ _
        rw [hu, one_smul]
        rcases TauCeti.eq_mk_one_or_eq_mk_of_index_two bot_index_twoGroup
          twoGroupGen_notMem_bot x with rfl | rfl
        · rw [Equiv.swap_apply_left, TauCeti.smul_mk_one_of_notMem_of_index_two bot_index_twoGroup
            twoGroupGen_notMem_bot hinv]
        · rw [Equiv.swap_apply_right, TauCeti.smul_mk_of_notMem_of_index_two bot_index_twoGroup
            twoGroupGen_notMem_bot hinv]
      | add y z hy hz => simp only [map_add, hy, hz]
    rw [hperm, Subgroup.tensorInducedMulAlgHom_tensorInducedAlgAut]

end Examples
