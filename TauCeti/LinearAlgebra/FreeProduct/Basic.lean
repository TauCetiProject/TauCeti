/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.FreeProduct.Basic

/-!
# Basic universal-property API for algebraic free products

This file supplements Mathlib's `LinearAlgebra.FreeProduct` with pointwise evaluation,
extensionality, factor-generation, induction, and empty-index lemmas for unital `R`-algebras.

## Main definitions

* `LinearAlgebra.FreeProduct.isEmptyAlgEquiv`: the unital algebraic free product over an empty index
  type is canonically `R`-algebra isomorphic to `R`.

## Main results

* `LinearAlgebra.FreeProduct.algHom_ext`: algebra homomorphisms out of `FreeProduct R A` are
  determined by their values on the canonical factor embeddings `LinearAlgebra.FreeProduct.ι`.
* `LinearAlgebra.FreeProduct.lift_ι_apply`, `LinearAlgebra.FreeProduct.lift_comp`, and
  `LinearAlgebra.FreeProduct.lift_ι`: pointwise evaluation and functoriality of
  `LinearAlgebra.FreeProduct.lift`.
* `LinearAlgebra.FreeProduct.iSup_range_ι` and `LinearAlgebra.FreeProduct.adjoin_iUnion_range_ι`:
  the images of the canonical factor maps generate `FreeProduct R A` as a unital `R`-subalgebra.
* `LinearAlgebra.FreeProduct.induction_on`: structural induction on `FreeProduct R A` from scalars
  and factor images under addition and multiplication.
-/

public section

namespace LinearAlgebra.FreeProduct

variable {I : Type*} [DecidableEq I] (R : Type*) [CommSemiring R]
  (A : I → Type*) [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

/-- Evaluating a lifted algebra homomorphism on an element of the `i`-th factor recovers the `i`-th
prescribed map. -/
@[simp↓]
theorem lift_ι_apply {B : Type*} [Semiring B] [Algebra R B]
    (maps : {i : I} → A i →ₐ[R] B) (i : I) (a : A i) :
    lift R A maps (ι R A i a) = maps a :=
  AlgHom.congr_fun (lift_comp_ι R A maps (i := i)) a

section Ext

variable {R A} {B : Type*} [Semiring B] [Algebra R B]

/-- Algebra homomorphisms out of `FreeProduct R A` are determined by their restrictions to the
factors. -/
@[ext]
theorem algHom_ext {f g : FreeProduct R A →ₐ[R] B}
    (h : ∀ i a, f (ι R A i a) = g (ι R A i a)) : f = g := by
  apply (lift R A).symm.injective
  funext i
  exact AlgHom.ext (h i)

/-- Postcomposing a lifted algebra homomorphism agrees with lifting the postcomposed factor maps. -/
@[simp↓]
theorem lift_comp {C : Type*} [Semiring C] [Algebra R C]
    (maps : {i : I} → A i →ₐ[R] B) (g : B →ₐ[R] C) :
    lift R A (fun {i} ↦ g.comp (maps (i := i))) = g.comp (lift R A maps) := by
  refine algHom_ext fun i a ↦ ?_
  rw [lift_ι_apply, AlgHom.comp_apply, AlgHom.comp_apply, lift_ι_apply]

end Ext

/-- Lifting the canonical factor embeddings gives the identity homomorphism. -/
@[simp↓]
theorem lift_ι : lift R A (fun {i} ↦ ι R A i) = AlgHom.id R (FreeProduct R A) :=
  algHom_ext fun i a ↦ lift_ι_apply R A _ i a

/-- The images of the factor embeddings generate the entire algebraic free product as a unital
subalgebra. -/
theorem iSup_range_ι : (⨆ i, (ι R A i).range) = (⊤ : Subalgebra R (FreeProduct R A)) := by
  let S : Subalgebra R (FreeProduct R A) := ⨆ i, (ι R A i).range
  let s : FreeProduct R A →ₐ[R] S :=
    lift R A fun {i} ↦ (ι R A i).codRestrict S fun a ↦
      le_iSup (fun j ↦ (ι R A j).range) i ⟨a, rfl⟩
  have hs : S.val.comp s = AlgHom.id R (FreeProduct R A) := by
    refine algHom_ext fun i a ↦ ?_
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    exact congrArg S.val (lift_ι_apply R A _ i a)
  rw [eq_top_iff]
  intro x _
  have hx : S.val (s x) = x := AlgHom.congr_fun hs x
  exact hx ▸ (s x).2

/-- The union of the ranges of the factor maps generates `FreeProduct R A` over `R`. -/
theorem adjoin_iUnion_range_ι :
    Algebra.adjoin R (⋃ i, Set.range (ι R A i)) = (⊤ : Subalgebra R (FreeProduct R A)) := by
  rw [Algebra.adjoin_iUnion]
  simpa only [← AlgHom.coe_range, Algebra.adjoin_eq] using iSup_range_ι R A

section Induction

variable {R A}

/-- Induction principle for `FreeProduct R A`: a property holding on scalars and on every factor
image, and closed under addition and multiplication, holds everywhere on `FreeProduct R A`. -/
@[elab_as_elim]
theorem induction_on {motive : FreeProduct R A → Prop} (x : FreeProduct R A)
    (algebraMap : ∀ r : R, motive (algebraMap R (FreeProduct R A) r))
    (ι : ∀ (i : I) (a : A i), motive (FreeProduct.ι R A i a))
    (mul : ∀ x y, motive x → motive y → motive (x * y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x := by
  let T : Subalgebra R (FreeProduct R A) :=
    { carrier := {y | motive y}
      mul_mem' {a b} := mul a b
      add_mem' {a b} := add a b
      algebraMap_mem' := algebraMap }
  have hT : (⊤ : Subalgebra R (FreeProduct R A)) ≤ T := by
    rw [← iSup_range_ι R A, iSup_le_iff]
    rintro i _ ⟨a, rfl⟩
    exact ι i a
  exact hT Algebra.mem_top

end Induction

/-- The unital algebraic free product over an empty index type is canonically isomorphic to the base
semiring `R`. -/
noncomputable def isEmptyAlgEquiv [IsEmpty I] : FreeProduct R A ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom
    (lift R A fun {i} ↦ isEmptyElim i)
    (Algebra.ofId R (FreeProduct R A))
    (AlgHom.ext fun r ↦ lift_algebraMap R A _ r)
    (algHom_ext fun i ↦ isEmptyElim i)

/-- On scalars, `isEmptyAlgEquiv` is the identity (`simp` already discharges this via
`AlgEquiv.commutes`). -/
theorem isEmptyAlgEquiv_algebraMap [IsEmpty I] (r : R) :
    isEmptyAlgEquiv R A (algebraMap R (FreeProduct R A) r) = r :=
  lift_algebraMap R A _ r

@[simp]
theorem isEmptyAlgEquiv_symm_apply [IsEmpty I] (r : R) :
    (isEmptyAlgEquiv R A).symm r = algebraMap R (FreeProduct R A) r :=
  (rfl)

end LinearAlgebra.FreeProduct
