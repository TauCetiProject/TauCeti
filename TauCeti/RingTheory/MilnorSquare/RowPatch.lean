/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Opposite
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Opposite
public import TauCeti.RingTheory.MilnorSquare.PatchedModule
public import TauCeti.RingTheory.Pullback.Opposite

/-!
# Row patching and the opposite ring

For a fibre product `D = A₁ ×_Q A₂`, glue free left modules by a transition matrix
`a ∈ GLₙ(Q)` from the second endpoint to the first. The row patch consists of pairs
`(p, q)` satisfying `π₁(p) = π₂(q) a`, with componentwise left scalar multiplication.

Taking opposite coefficients converts this equation to the column equation with transition
`aᵀ`. The library construction `RingHom.patchedSubgroup` takes a first-to-second parameter,
so it is evaluated at the inverse of that transpose. The semilinear equivalence
`RingHom.patchedSubgroupOpEquivRowPatch` identifies the two patches for arbitrary legs.
Surjectivity of either leg gives finiteness and projectivity of the row patch.

The equivalences `RingHom.rowPatchOneEquiv`, `RingHom.rowPatchProdEquiv`,
`RingHom.rowPatchProdOneEquiv`, and `RingHom.rowPatchEquivOfMul` describe the identity
transition, block sums, identity padding, and changes of endpoint trivializations.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, §2.7.
* J. Milnor, *Introduction to Algebraic K-Theory*, §2.
-/

public section

noncomputable section

open Matrix Matrix.GeneralLinearGroup MulOpposite

namespace RingHom

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q]
  (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The left row patch for a transition from the second endpoint to the first. -/
def rowPatch (a : GL n Q) : AddSubgroup ((n → A₁) × (n → A₂)) :=
  AddMonoidHom.eqLocus ((π₁.toAddMonoidHom.compLeft n).comp (AddMonoidHom.fst _ _))
    ((AddMonoidHom.mk' (· ᵥ* (a : Matrix n n Q)) (add_vecMul _)).comp
      ((π₂.toAddMonoidHom.compLeft n).comp (AddMonoidHom.snd _ _)))

variable {π₁ π₂}

/-- The row transition sends the reduction of the second coordinate to that of the first. -/
@[simp]
theorem mem_rowPatch {a : GL n Q} {x : (n → A₁) × (n → A₂)} :
    x ∈ π₁.rowPatch π₂ a ↔ π₁ ∘ x.1 = (π₂ ∘ x.2) ᵥ* (a : Matrix n n Q) :=
  Iff.rfl

/-- Passing to opposite coefficients translates the column condition into the row condition. -/
private theorem mem_rowPatch_iff_op_mem_patchedSubgroup {a : GL n Q}
    {x : (n → A₁) × (n → A₂)} :
    x ∈ π₁.rowPatch π₂ a ↔ (MulOpposite.op ∘ x.1, MulOpposite.op ∘ x.2) ∈
      π₁.op.patchedSubgroup π₂.op (transposeOpEquiv a).unop⁻¹ := by
  rw [mem_rowPatch, mem_patchedSubgroup]
  let b := (transposeOpEquiv a).unop
  -- Invert the library's first-to-second parameter to write the equation in transition order.
  have hinv (p q : n → Qᵐᵒᵖ) :
      (↑(b⁻¹ : GL n Qᵐᵒᵖ) : Matrix n n Qᵐᵒᵖ) *ᵥ p = q ↔
        p = (b : Matrix n n Qᵐᵒᵖ) *ᵥ q := by
    constructor <;> intro h
    · simpa using congrArg ((b : Matrix n n Qᵐᵒᵖ) *ᵥ ·) h
    · simp [h]
  rw [hinv]
  have hop (v : n → Q) :
      (b : Matrix n n Qᵐᵒᵖ) *ᵥ (MulOpposite.op ∘ v) =
        MulOpposite.op ∘ (v ᵥ* (a : Matrix n n Q)) := by
    ext i
    simp [b, mulVec, vecMul, dotProduct]
  -- The opposite coefficient maps are pointwise `op ∘ πᵢ ∘ unop`.
  change _ ↔ MulOpposite.op ∘ (π₁ ∘ x.1) =
    (b : Matrix n n Qᵐᵒᵖ) *ᵥ (MulOpposite.op ∘ (π₂ ∘ x.2))
  rw [hop]
  exact (Function.Injective.comp_left op_injective).eq_iff.symm

private def patchedSubgroupOpAddEquiv (a : GL n Q) :
    π₁.op.patchedSubgroup π₂.op (transposeOpEquiv a).unop⁻¹ ≃+ π₁.rowPatch π₂ a where
  toFun x := ⟨(MulOpposite.unop ∘ x.val.1, MulOpposite.unop ∘ x.val.2),
    mem_rowPatch_iff_op_mem_patchedSubgroup.mpr x.property⟩
  invFun x := ⟨(MulOpposite.op ∘ x.val.1, MulOpposite.op ∘ x.val.2),
    mem_rowPatch_iff_op_mem_patchedSubgroup.mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem smul_mem_rowPatch {a : GL n Q} {x : (n → A₁) × (n → A₂)}
    (hx : x ∈ π₁.rowPatch π₂ a) (d : π₁.pullback π₂) :
    ((π₁.pullbackFst π₂ d) • x.1, (π₁.pullbackSnd π₂ d) • x.2) ∈ π₁.rowPatch π₂ a := by
  have hd : π₁ (π₁.pullbackFst π₂ d) = π₂ (π₁.pullbackSnd π₂ d) :=
    DFunLike.congr_fun (π₁.pullback_comm_sq π₂) d
  have h₁ : π₁ ∘ ((π₁.pullbackFst π₂ d) • x.1) =
      π₁ (π₁.pullbackFst π₂ d) • (π₁ ∘ x.1) := funext fun _ ↦ by simp
  have h₂ : π₂ ∘ ((π₁.pullbackSnd π₂ d) • x.2) =
      π₂ (π₁.pullbackSnd π₂ d) • (π₂ ∘ x.2) := funext fun _ ↦ by simp
  rw [mem_rowPatch] at hx ⊢
  rw [h₁, h₂, smul_vecMul, hx, hd]

/-- The row patch is a left module over the fibre product. -/
@[no_expose]
instance rowPatch.instModule (a : GL n Q) : Module (π₁.pullback π₂) (π₁.rowPatch π₂ a) :=
  letI : SMul (π₁.pullback π₂) (π₁.rowPatch π₂ a) :=
    ⟨fun d x ↦ ⟨_, smul_mem_rowPatch x.property d⟩⟩
  letI := Module.compHom (n → A₁) (π₁.pullbackFst π₂)
  letI := Module.compHom (n → A₂) (π₁.pullbackSnd π₂)
  Function.Injective.module _ (π₁.rowPatch π₂ a).subtype Subtype.val_injective fun _ _ ↦ rfl

/-- The two coordinates of the row patch carry the two left endpoint actions. -/
theorem rowPatch.coe_smul (a : GL n Q) (d : π₁.pullback π₂) (x : π₁.rowPatch π₂ a) :
    (↑(d • x) : (n → A₁) × (n → A₂)) =
      ((π₁.pullbackFst π₂ d) • x.val.1, (π₁.pullbackSnd π₂ d) • x.val.2) :=
  (rfl)

variable (π₁ π₂) in
/-- The right column patch over the opposite rings identifies with the left row patch by
returning each coordinate to its original ring. -/
def patchedSubgroupOpEquivRowPatch (a : GL n Q) :
    π₁.op.patchedSubgroup π₂.op (transposeOpEquiv a).unop⁻¹
      ≃ₛₗ[(π₁.pullbackOpOpEquiv π₂).toRingHom] π₁.rowPatch π₂ a :=
  { patchedSubgroupOpAddEquiv a with
    map_smul' := fun d x ↦ by
      apply Subtype.ext
      -- The additive equivalence unops coordinates before comparing scalar actions.
      change (MulOpposite.unop ∘ (d • x).val.1, MulOpposite.unop ∘ (d • x).val.2) = _
      rw [patchedSubgroup.coe_smul, rowPatch.coe_smul]
      apply Prod.ext <;> funext i <;>
        simp [patchedSubgroupOpAddEquiv, Function.comp_def, Pi.smul_apply] }

/-- The patch comparison returns each column coordinate from the opposite ring. -/
@[simp]
theorem coe_patchedSubgroupOpEquivRowPatch_apply (a : GL n Q)
    (x : π₁.op.patchedSubgroup π₂.op (transposeOpEquiv a).unop⁻¹) :
    (↑(patchedSubgroupOpEquivRowPatch π₁ π₂ a x) : (n → A₁) × (n → A₂)) =
      (MulOpposite.unop ∘ x.val.1, MulOpposite.unop ∘ x.val.2) :=
  (rfl)

/-- The inverse patch comparison sends each row coordinate to the opposite ring. -/
@[simp]
theorem coe_patchedSubgroupOpEquivRowPatch_symm_apply (a : GL n Q) (x : π₁.rowPatch π₂ a) :
    (↑((patchedSubgroupOpEquivRowPatch π₁ π₂ a).symm x) : (n → A₁ᵐᵒᵖ) × (n → A₂ᵐᵒᵖ)) =
      (MulOpposite.op ∘ x.val.1, MulOpposite.op ∘ x.val.2) :=
  (rfl)

/-- With either leg surjective, the left row patch is finitely generated. -/
theorem finite_rowPatch (h : Function.Surjective π₁ ∨ Function.Surjective π₂) (a : GL n Q) :
    Module.Finite (π₁.pullback π₂) (π₁.rowPatch π₂ a) :=
  letI := finite_patchedSubgroup (π₁ := π₁.op) (π₂ := π₂.op)
    (by simpa using h) (transposeOpEquiv a).unop⁻¹
  Module.Finite.of_surjective (patchedSubgroupOpEquivRowPatch π₁ π₂ a).toLinearMap
    (patchedSubgroupOpEquivRowPatch π₁ π₂ a).surjective

/-- With either leg surjective, the left row patch is projective. -/
theorem projective_rowPatch (h : Function.Surjective π₁ ∨ Function.Surjective π₂) (a : GL n Q) :
    Module.Projective (π₁.pullback π₂) (π₁.rowPatch π₂ a) :=
  letI := projective_patchedSubgroup (π₁ := π₁.op) (π₂ := π₂.op)
    (by simpa using h) (transposeOpEquiv a).unop⁻¹
  Module.Projective.of_equiv (patchedSubgroupOpEquivRowPatch π₁ π₂ a)

/-- The identity transition glues the two free modules to a free module over the fibre product. -/
def rowPatchOneEquiv (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q) (n : Type*)
    [Fintype n] [DecidableEq n] :
    π₁.rowPatch π₂ (1 : GL n Q) ≃ₗ[π₁.pullback π₂] (n → π₁.pullback π₂) where
  toFun x i := ⟨(x.val.1 i, x.val.2 i), by
    simpa using congrFun (mem_rowPatch.mp x.property) i⟩
  invFun v := ⟨(fun i ↦ (v i).val.1, fun i ↦ (v i).val.2), by
    rw [mem_rowPatch, Units.val_one, vecMul_one]
    exact funext fun i ↦ (v i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' d x := funext fun i ↦ Subtype.ext <| by
    simp [rowPatch.coe_smul, Pi.smul_apply, Prod.mul_def]

/-- The identity patch groups the two entries at each index into a fibre product coordinate. -/
@[simp]
theorem coe_rowPatchOneEquiv_apply (x : π₁.rowPatch π₂ (1 : GL n Q)) (i : n) :
    (rowPatchOneEquiv π₁ π₂ n x i : A₁ × A₂) = (x.val.1 i, x.val.2 i) :=
  (rfl)

/-- The inverse of the identity patch comparison takes the two endpoint coordinates. -/
@[simp]
theorem coe_rowPatchOneEquiv_symm_apply (v : n → π₁.pullback π₂) :
    ((rowPatchOneEquiv π₁ π₂ n).symm v).val =
      (fun i ↦ (v i).val.1, fun i ↦ (v i).val.2) :=
  (rfl)

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A pair of rows patched along a block diagonal satisfies the two independent patch
equations on its blocks. -/
theorem mem_rowPatch_fromBlocksGL {a : GL n Q} {b : GL m Q}
    {x : (n ⊕ m → A₁) × (n ⊕ m → A₂)} :
    x ∈ π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, b)) ↔
      (x.1 ∘ Sum.inl, x.2 ∘ Sum.inl) ∈ π₁.rowPatch π₂ a ∧
      (x.1 ∘ Sum.inr, x.2 ∘ Sum.inr) ∈ π₁.rowPatch π₂ b := by
  simp only [mem_rowPatch, TauCeti.coe_fromBlocksGL, vecMul_fromBlocks, vecMul_zero, add_zero,
    zero_add, Function.comp_assoc]
  constructor
  · intro h
    exact ⟨congrArg (· ∘ Sum.inl) h, congrArg (· ∘ Sum.inr) h⟩
  · rintro ⟨h₁, h₂⟩
    exact funext fun
      | .inl i => congrFun h₁ i
      | .inr i => congrFun h₂ i

variable (π₁ π₂) in
/-- The row patch of a block diagonal is the direct sum of the row patches. -/
def rowPatchProdEquiv (a : GL n Q) (b : GL m Q) :
    (π₁.rowPatch π₂ a × π₁.rowPatch π₂ b) ≃ₗ[π₁.pullback π₂]
      π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, b)) where
  toFun x := ⟨(Sum.elim x.1.val.1 x.2.val.1, Sum.elim x.1.val.2 x.2.val.2),
    mem_rowPatch_fromBlocksGL.mpr ⟨x.1.property, x.2.property⟩⟩
  invFun x := (⟨_, (mem_rowPatch_fromBlocksGL.mp x.property).1⟩,
    ⟨_, (mem_rowPatch_fromBlocksGL.mp x.property).2⟩)
  left_inv _ := rfl
  right_inv x := Subtype.ext <| Prod.ext (Sum.elim_comp_inl_inr _) (Sum.elim_comp_inl_inr _)
  map_add' x y := Subtype.ext <| Prod.ext (by ext (i | i) <;> simp) (by ext (i | i) <;> simp)
  map_smul' d x := Subtype.ext <| Prod.ext
    (by ext (i | i) <;> simp [rowPatch.coe_smul])
    (by ext (i | i) <;> simp [rowPatch.coe_smul])

/-- The block-sum comparison concatenates the two rows on each endpoint. -/
@[simp]
theorem coe_rowPatchProdEquiv_apply {a : GL n Q} {b : GL m Q}
    (x : π₁.rowPatch π₂ a × π₁.rowPatch π₂ b) :
    (rowPatchProdEquiv π₁ π₂ a b x).val =
      (Sum.elim x.1.val.1 x.2.val.1, Sum.elim x.1.val.2 x.2.val.2) :=
  (rfl)

/-- The first block is recovered by restricting both rows to the left indices. -/
@[simp]
theorem coe_rowPatchProdEquiv_symm_apply_fst {a : GL n Q} {b : GL m Q}
    (x : π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, b))) :
    ((rowPatchProdEquiv π₁ π₂ a b).symm x).1.val = (x.val.1 ∘ Sum.inl, x.val.2 ∘ Sum.inl) :=
  (rfl)

/-- The second block is recovered by restricting both rows to the right indices. -/
@[simp]
theorem coe_rowPatchProdEquiv_symm_apply_snd {a : GL n Q} {b : GL m Q}
    (x : π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, b))) :
    ((rowPatchProdEquiv π₁ π₂ a b).symm x).2.val = (x.val.1 ∘ Sum.inr, x.val.2 ∘ Sum.inr) :=
  (rfl)

variable (π₁ π₂) in
/-- Padding a transition with an identity block adds a free summand to its row patch. -/
def rowPatchProdOneEquiv (a : GL n Q) (m : Type*) [Fintype m] [DecidableEq m] :
    (π₁.rowPatch π₂ a × (m → π₁.pullback π₂)) ≃ₗ[π₁.pullback π₂]
      π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, (1 : GL m Q))) :=
  ((LinearEquiv.refl _ _).prodCongr (rowPatchOneEquiv π₁ π₂ m).symm).trans
    (rowPatchProdEquiv π₁ π₂ a 1)

/-- Identity padding concatenates the row coordinates with the endpoint projections
of the free summand. -/
@[simp]
theorem coe_rowPatchProdOneEquiv_apply (a : GL n Q)
    (x : π₁.rowPatch π₂ a) (v : m → π₁.pullback π₂) :
    (rowPatchProdOneEquiv π₁ π₂ a m (x, v)).val =
      (Sum.elim x.val.1 (fun i ↦ (v i).val.1), Sum.elim x.val.2 (fun i ↦ (v i).val.2)) := by
  simp [rowPatchProdOneEquiv]

/-- The inverse padding comparison restricts the patched part to the left indices. -/
@[simp]
theorem coe_rowPatchProdOneEquiv_symm_apply_fst {a : GL n Q}
    (x : π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, (1 : GL m Q)))) :
    ((rowPatchProdOneEquiv π₁ π₂ a m).symm x).1.val = (x.val.1 ∘ Sum.inl, x.val.2 ∘ Sum.inl) :=
  (rfl)

/-- The inverse padding comparison groups the right entries into fibre product coordinates. -/
@[simp]
theorem coe_rowPatchProdOneEquiv_symm_apply_snd {a : GL n Q}
    (x : π₁.rowPatch π₂ (TauCeti.fromBlocksGL (a, (1 : GL m Q)))) (i : m) :
    (((rowPatchProdOneEquiv π₁ π₂ a m).symm x).2 i : A₁ × A₂) =
      (x.val.1 (Sum.inr i), x.val.2 (Sum.inr i)) :=
  (rfl)

/-- If `a π₁(X₁) = π₂(X₂) b` for rectangular matrices `X₁` and `X₂`, then right multiplication
by these matrices sends the row patch for `a` into the row patch for `b`. -/
theorem vecMul_mem_rowPatch {a : GL n Q} {b : GL m Q} {X₁ : Matrix n m A₁}
    {X₂ : Matrix n m A₂} (h : (a : Matrix n n Q) * X₁.map π₁ = X₂.map π₂ * (b : Matrix m m Q))
    {x : (n → A₁) × (n → A₂)} (hx : x ∈ π₁.rowPatch π₂ a) :
    (x.1 ᵥ* X₁, x.2 ᵥ* X₂) ∈ π₁.rowPatch π₂ b := by
  have h₁ : π₁ ∘ (x.1 ᵥ* X₁) = (π₁ ∘ x.1) ᵥ* X₁.map π₁ := funext (π₁.map_vecMul _ _)
  have h₂ : π₂ ∘ (x.2 ᵥ* X₂) = (π₂ ∘ x.2) ᵥ* X₂.map π₂ := funext (π₂.map_vecMul _ _)
  rw [mem_rowPatch] at hx ⊢
  dsimp only
  rw [h₁, h₂, hx, vecMul_vecMul, vecMul_vecMul, h]

variable (π₁ π₂) in
/-- Changes of the two free trivializations act on the rows by right multiplication. -/
def rowPatchEquivOfMul {a b : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : a * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * b) :
    π₁.rowPatch π₂ a ≃ₗ[π₁.pullback π₂] π₁.rowPatch π₂ b where
  toFun x := ⟨(x.val.1 ᵥ* ↑g₁, x.val.2 ᵥ* ↑g₂),
    vecMul_mem_rowPatch (congrArg Units.val h) x.property⟩
  invFun x :=
    have hinv : b * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁⁻¹ =
        Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂⁻¹ * a := by
      rw [map_inv, map_inv, mul_inv_eq_iff_eq_mul, mul_assoc, h, inv_mul_cancel_left]
    ⟨(x.val.1 ᵥ* ↑g₁⁻¹, x.val.2 ᵥ* ↑g₂⁻¹),
      vecMul_mem_rowPatch (congrArg Units.val hinv) x.property⟩
  left_inv x := Subtype.ext <| Prod.ext (by simp) (by simp)
  right_inv x := Subtype.ext <| Prod.ext (by simp) (by simp)
  map_add' x y := Subtype.ext <| Prod.ext (by simp [add_vecMul]) (by simp [add_vecMul])
  map_smul' d x := Subtype.ext <| by simp [rowPatch.coe_smul, smul_vecMul]

/-- Changing either endpoint trivialization multiplies the corresponding coordinate on the right. -/
@[simp]
theorem coe_rowPatchEquivOfMul_apply {a b : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : a * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * b) (x : π₁.rowPatch π₂ a) :
    (rowPatchEquivOfMul π₁ π₂ g₁ g₂ h x).val =
      (x.val.1 ᵥ* (g₁ : Matrix n n A₁), x.val.2 ᵥ* (g₂ : Matrix n n A₂)) :=
  (rfl)

/-- The inverse change of trivializations multiplies each row by the inverse endpoint matrix. -/
@[simp]
theorem coe_rowPatchEquivOfMul_symm_apply {a b : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : a * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * b) (x : π₁.rowPatch π₂ b) :
    ((rowPatchEquivOfMul π₁ π₂ g₁ g₂ h).symm x).val =
      (x.val.1 ᵥ* ↑g₁⁻¹, x.val.2 ᵥ* ↑g₂⁻¹) :=
  (rfl)

end RingHom
