/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Contracting two slots of an indexed tensor power

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
        funext fun b => update_of_ne (by rintro rfl; exact ha b.2) ..
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
  have hw (a : {a : ι // a ≠ i ∧ a ≠ j}) : ¬(a : ι) = i ∧ ¬(a : ι) = j := a.2
  simp [hij.symm, hw]

end LinearMap
