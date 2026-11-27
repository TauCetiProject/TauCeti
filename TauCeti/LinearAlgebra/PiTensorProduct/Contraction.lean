/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Contracting slots of an indexed tensor power

A bilinear form contracts two distinct slots of a tensor power and leaves the other slots
unchanged. The output is indexed by the complement of those two slots, avoiding a choice of
ordering on the remaining factors. For a finite index set of size `d`, this is a tensor power
with `d - 2` factors.

`LinearMap.contractTensorPair` is characterized on pure tensors and commutes with diagonal
maps intertwining the pairings. These are the trace maps used to define harmonic tensors for
orthogonal and symplectic representations.

In the other direction, `PiTensorProduct.insertPair` raises the degree by two: it places two
chosen vectors in the two slots and keeps the other factors. Contracting the same two slots
afterwards multiplies by the pairing of the two inserted vectors
(`LinearMap.contractTensorPair_comp_insertPair`). Inserting a copairing this way is how a cup
re-expands two contracted slots, so a single arc of a Brauer diagram factors as an insertion after
a contraction.

For finite sets `S ⊆ T` of indices, `PiTensorProduct.contractMultilinear` contracts the slots of
`T \ S` against linear forms and keeps the slots of `S`: a family `g` over `T` goes to the pure
tensor of `g` on `S`, scaled by the product of the forms evaluated at `g` on `T \ S`
(`PiTensorProduct.contractMultilinear_apply`).
-/

public section

open Function
open scoped TensorProduct

namespace LinearMap

universe u v w

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {ι : Type w}

private noncomputable def contractTensorPairMultilinear (B : LinearMap.BilinForm R M)
    (i j : ι) (hij : i ≠ j) :
    MultilinearMap (RingHom.id R) (fun _ : ι => M) (⨂[R] _ : {a : ι // a ≠ i ∧ a ≠ j}, M) := by
  classical
  refine MultilinearMap.mk'
    (fun v => B (v i) (v j) •
      PiTensorProduct.tprod R (fun a : {a : ι // a ≠ i ∧ a ≠ j} => v a.val)) ?_ ?_
  all_goals
    intro v a
    by_cases ha : a ≠ i ∧ a ≠ j
    · have hup (z : M) : (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v a z b.val) =
          update (fun b => v b.val) ⟨a, ha⟩ z :=
        update_comp_eq_of_injective v Subtype.val_injective ⟨a, ha⟩ z
      simp [hup, update_of_ne ha.1.symm, update_of_ne ha.2.symm, smul_comm (B (v i) (v j))]
    · have hup (z : M) : (fun b : {b : ι // b ≠ i ∧ b ≠ j} => update v a z b.val) =
          fun b => v b.val :=
        funext fun b => update_of_ne (by rintro rfl; exact ha b.property) ..
      obtain rfl | rfl : a = i ∨ a = j := by tauto
      · simp [hup, update_of_ne hij.symm, add_smul, mul_smul]
      · simp [hup, update_of_ne hij, add_smul, mul_smul]

/-- Contract two distinct slots against a bilinear form. The remaining factors keep their
original indices, restricted to the complement of the contracted pair. -/
noncomputable def contractTensorPair (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j) :
    (⨂[R] _ : ι, M) →ₗ[R] ⨂[R] _ : {a : ι // a ≠ i ∧ a ≠ j}, M :=
  PiTensorProduct.lift (contractTensorPairMultilinear B i j hij)

/-- On pure tensors, contraction pairs the selected factors and retains the others. -/
@[simp]
theorem contractTensorPair_tprod (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j) (v : ι → M) :
    B.contractTensorPair i j hij (PiTensorProduct.tprod R v) =
      B (v i) (v j) • PiTensorProduct.tprod R (fun a : {a : ι // a ≠ i ∧ a ≠ j} => v a.val) := by
  classical
  rw [contractTensorPair, PiTensorProduct.lift.tprod]
  rfl

/-- Contraction commutes with a diagonal linear map intertwining the bilinear pairings. -/
theorem contractTensorPair_comp_map {N : Type*} [AddCommMonoid N] [Module R N]
    (B : LinearMap.BilinForm R M) (B' : LinearMap.BilinForm R N) (i j : ι) (hij : i ≠ j)
    (f : M →ₗ[R] N) (hf : ∀ x y, B' (f x) (f y) = B x y) :
    B'.contractTensorPair i j hij ∘ₗ PiTensorProduct.map (fun _ : ι => f) =
      PiTensorProduct.map (fun _ : {a : ι // a ≠ i ∧ a ≠ j} => f) ∘ₗ
        B.contractTensorPair i j hij := by
  apply PiTensorProduct.ext
  ext v
  simp [hf]

/-- Renaming the slots renames a contracted pair and the complementary output slots. -/
theorem contractTensorPair_reindex (B : LinearMap.BilinForm R M) (i j : ι) (hij : i ≠ j)
    {κ : Type*} (e : ι ≃ κ) (x : ⨂[R] _ : ι, M) :
    B.contractTensorPair (e i) (e j) (e.injective.ne hij)
        (PiTensorProduct.reindex R (fun _ : ι => M) e x) =
      PiTensorProduct.reindex R (fun _ : {a : ι // a ≠ i ∧ a ≠ j} => M)
        (e.subtypeEquiv fun _ => (and_congr e.injective.ne_iff e.injective.ne_iff).symm)
        (B.contractTensorPair i j hij x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    -- The induction principle hands over `v` at a dependent function type, under which
    -- `simp` cannot rewrite its argument.
    beta_reduce at v
    simp
  | add x y hx hy => simp only [map_add, hx, hy]

end LinearMap

/-! ### Inserting two vectors into two slots -/

namespace PiTensorProduct

variable (R : Type*) [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {ι : Type*} [DecidableEq ι]

/-- Insert two vectors into two slots of a tensor power: `p` into the slot `i`, `q` into the slot
`j` when `i ≠ j`, and every other factor kept at its index. When `i = j` only `p` is inserted and
`q` is ignored. Against a bilinear form, contracting the same two distinct slots undoes it up to
the pairing of `p` and `q` (`LinearMap.contractTensorPair_comp_insertPair`). -/
noncomputable def insertPair (i j : ι) (p q : M) :
    (⨂[R] _ : {a : ι // a ≠ i ∧ a ≠ j}, M) →ₗ[R] ⨂[R] _ : ι, M :=
  lift <| (tprod R (s := fun _ : ι => M)).domDomRestrict (fun a => a ≠ i ∧ a ≠ j)
    fun a => if a.val = i then p else q

variable {R}

/-- On a pure tensor, insertion fills the slot `i` with `p`, the slot `j` with `q` when `i ≠ j`,
and every other slot with the corresponding factor. When `i = j` that slot holds `p`. -/
@[simp]
theorem insertPair_tprod (i j : ι) (p q : M) (w : {a : ι // a ≠ i ∧ a ≠ j} → M) :
    insertPair R i j p q (tprod R w) =
      tprod R fun a => if h : a ≠ i ∧ a ≠ j then w ⟨a, h⟩ else if a = i then p else q := by
  rw [insertPair, lift.tprod, MultilinearMap.domDomRestrict_apply]

end PiTensorProduct

namespace LinearMap

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {ι : Type*} [DecidableEq ι]

/-- **Contraction after insertion.** Inserting `p` and `q` into two distinct slots and then
contracting those slots against `B` is multiplication by `B p q`. -/
theorem contractTensorPair_comp_insertPair (B : LinearMap.BilinForm R M) {i j : ι} (hij : i ≠ j)
    (p q : M) :
    B.contractTensorPair i j hij ∘ₗ PiTensorProduct.insertPair R i j p q =
      B p q • LinearMap.id := by
  ext w
  have hw (a : {a : ι // a ≠ i ∧ a ≠ j}) : ¬(a : ι) = i ∧ ¬(a : ι) = j := a.property
  simp [hij.symm, hw]

end LinearMap

/-! ### Contracting a block of slots against linear forms -/

namespace PiTensorProduct

variable {ι : Type*} [DecidableEq ι] {W : ι → Type*} (R : Type*) [CommSemiring R]
  [∀ i, AddCommMonoid (W i)] [∀ i, Module R (W i)] {S T : Finset ι} (h : S ⊆ T)

/-- Contracting the places of `T \ S` against linear forms, as a multilinear map: the tensor
product of the pure tensor over `S` with the product of the forms over `T \ S`, followed by
`M ⊗ R ≃ M`. -/
noncomputable def contractMultilinear (φ : ∀ i, Module.Dual R (W i)) :
    (Π i : T, W i) →ₘₗ[R] ⨂[R] i : S, W i :=
  (TensorProduct.rid R _).toLinearMap.compMultilinearMap <|
    (MultilinearMap.domDomCongrLinearEquiv' R (RingHom.id R) (fun i : T ↦ W i) _
      (Equiv.sumCompl fun i : T ↦ i.val ∈ S).symm).symm
      (MultilinearMap.domCoprodDep
        ((MultilinearMap.domDomCongrLinearEquiv' R (RingHom.id R)
          (fun i : {a : T // a.val ∈ S} ↦ W i) _
          (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ T)) (q := (· ∈ S)) (h ·))).symm
          (tprod R (s := fun i : S ↦ W i)))
        ((MultilinearMap.mkPiAlgebra R {i : T // i.val ∉ S} R).compLinearMap fun i ↦ φ i))

variable {R}

/-- The contraction on a family of vectors. -/
@[simp]
theorem contractMultilinear_apply (φ : ∀ i, Module.Dual R (W i)) (g : ∀ i : T, W i) :
    contractMultilinear R h φ g = (∏ i : {i : T // i.val ∉ S}, φ i (g i)) •
      tprod R (fun i : S ↦ g ⟨i.val, h i.property⟩) := by
  rw [contractMultilinear, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domDomCongrLinearEquiv'_symm_apply]
  -- The reindexed entries are `g` at the corresponding places by definition of
  -- `Equiv.piCongrLeft'`, `Equiv.sumCompl` and `Equiv.subtypeSubtypeEquivSubtype`, so
  -- `domCoprodDep` evaluates to this tensor. Rewriting with
  -- `MultilinearMap.domCoprodDep_apply` instead fails: the reindexed `tprod` has the type
  -- expected there only up to unfolding these equivalences.
  change TensorProduct.rid R _ (tprod R (fun i : S ↦ g ⟨i.val, h i.property⟩) ⊗ₜ
    ∏ i : {i : T // i.val ∉ S}, φ i (g i)) = _
  exact TensorProduct.rid_tmul _ _

end PiTensorProduct
