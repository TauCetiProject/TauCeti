/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Patched modules over a fibre product of rings

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms between arbitrary (possibly
noncommutative) rings, and let `D = A₁ ×_Q A₂` be their fibre product, Mathlib's
`RingHom.pullback π₁ π₂`. For an invertible matrix `u ∈ GLₙ(Q)` the **patched module**

  `M(u) = {(a, b) ∈ A₁ⁿ × A₂ⁿ | u π₁(a) = π₂(b)}`

of column vectors is a right `D`-module, `(a, b) · (d₁, d₂) = (a d₁, b d₂)`; it is obtained by
gluing the free modules `A₁ⁿ` and `A₂ⁿ` along the automorphism `u` of `Qⁿ`. Following the
right-module convention of `TauCeti.KZero`, it is encoded as a left `Dᵐᵒᵖ`-module.

The patched modules satisfy:

* `M(1) ≅ Dⁿ`;
* `M(u) × M(v) ≅ M(u ⊕ v)` for the block diagonal matrix `u ⊕ v`;
* relabelling the indices of `u` does not change `M(u)`;
* `M(u) ≅ M(u')` whenever `u' π₁(g₁) = π₂(g₂) u` for invertible matrices `g₁` over `A₁` and
  `g₂` over `A₂`: the patched module only depends on the double coset of `u`.

When `π₁` or `π₂` is surjective, Whitehead's elementary matrix `u ⊕ u⁻¹` lifts to an invertible
matrix over that leg, so `M(u) × M(u⁻¹) ≅ M(u ⊕ u⁻¹) ≅ M(1) ≅ D²ⁿ`: the patched module is a direct
summand of a finite free module, hence finitely generated projective.

## Main definitions

* `RingHom.patchedSubgroup π₁ π₂ u`: the patched module `M(u)`, an additive subgroup of
  `A₁ⁿ × A₂ⁿ` with its right `D`-module structure.

## Main results

* `RingHom.patchedSubgroupOneEquiv`, `RingHom.patchedSubgroupProdEquiv`,
  `RingHom.patchedSubgroupReindexEquiv`, `RingHom.patchedSubgroupEquivOfMul`: the patched
  module of the identity, of a block diagonal matrix, of a relabelled matrix and of a matrix in
  the same double coset.
* `RingHom.nonempty_patchedSubgroup_elementary_equiv`: with one surjective leg, the patched
  module of an elementary matrix is free.
* `RingHom.nonempty_patchedSubgroup_prod_inv_equiv`: with one surjective leg,
  `M(u) × M(u⁻¹) ≅ D²ⁿ`.
* `RingHom.projective_patchedSubgroup`, `RingHom.finite_patchedSubgroup`: with one surjective
  leg, `M(u)` is finitely generated projective.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2
  (the projective modules `M(P₁, P₂, h)` over a fibre product, shown projective first for free
  `P₁`, `P₂` by lifting Whitehead's elementary matrix `h ⊕ h⁻¹`).
-/

public section

noncomputable section

open Matrix TauCeti

namespace RingHom

universe u₁ u₂ v

variable {A₁ : Type u₁} {A₂ : Type u₂} {Q : Type v} [Ring A₁] [Ring A₂] [Ring Q]
  (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ## The patched module -/

/-- **The patched module** `M(u) = {(a, b) ∈ A₁ⁿ × A₂ⁿ | u π₁(a) = π₂(b)}` of an invertible
matrix `u` over `Q`, for ring homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`. It is a right
module over the fibre product `π₁.pullback π₂`, encoded as a left module over its opposite ring
(`RingHom.patchedSubgroup.instModule`). -/
def patchedSubgroup (u : GL n Q) : AddSubgroup ((n → A₁) × (n → A₂)) :=
  AddMonoidHom.eqLocus
    ((AddMonoidHom.mk' ((u : Matrix n n Q) *ᵥ ·) (mulVec_add _)).comp
      ((π₁.toAddMonoidHom.compLeft n).comp (AddMonoidHom.fst _ _)))
    ((π₂.toAddMonoidHom.compLeft n).comp (AddMonoidHom.snd _ _))

variable {π₁ π₂}

/-- Membership in the patched module: `(a, b) ∈ M(u)` if and only if `u π₁(a) = π₂(b)`. -/
@[simp]
theorem mem_patchedSubgroup {u : GL n Q} {x : (n → A₁) × (n → A₂)} :
    x ∈ π₁.patchedSubgroup π₂ u ↔ (u : Matrix n n Q) *ᵥ (π₁ ∘ x.1) = π₂ ∘ x.2 :=
  Iff.rfl

/-- Multiplying both components of an element of `M(u)` on the right by the two components of an
element of the fibre product gives an element of `M(u)`. -/
theorem op_smul_mem_patchedSubgroup {u : GL n Q} {x : (n → A₁) × (n → A₂)}
    (hx : x ∈ π₁.patchedSubgroup π₂ u) (d : π₁.pullback π₂) :
    (MulOpposite.op (d : A₁ × A₂).1 • x.1, MulOpposite.op (d : A₁ × A₂).2 • x.2) ∈
      π₁.patchedSubgroup π₂ u := by
  have hd : π₁ (d : A₁ × A₂).1 = π₂ (d : A₁ × A₂).2 := d.property
  have h₁ : π₁ ∘ (MulOpposite.op (d : A₁ × A₂).1 • x.1) =
      MulOpposite.op (π₁ (d : A₁ × A₂).1) • (π₁ ∘ x.1) := funext fun _ ↦ by simp
  have h₂ : π₂ ∘ (MulOpposite.op (d : A₁ × A₂).2 • x.2) =
      MulOpposite.op (π₂ (d : A₁ × A₂).2) • (π₂ ∘ x.2) := funext fun _ ↦ by simp
  rw [mem_patchedSubgroup] at hx ⊢
  rw [h₁, h₂, mulVec_smul, hx, hd]

namespace patchedSubgroup

variable {u : GL n Q}

/-- The right action of the fibre product `D = π₁.pullback π₂` on the patched module,
`(a, b) · (d₁, d₂) = (a d₁, b d₂)`, as a left action of `Dᵐᵒᵖ`. -/
instance instSMul : SMul (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) where
  smul d x := ⟨_, op_smul_mem_patchedSubgroup x.property d.unop⟩

@[simp]
theorem coe_smul (d : (π₁.pullback π₂)ᵐᵒᵖ) (x : π₁.patchedSubgroup π₂ u) :
    ((d • x : π₁.patchedSubgroup π₂ u) : (n → A₁) × (n → A₂)) =
      (MulOpposite.op (d.unop : A₁ × A₂).1 • (x : (n → A₁) × (n → A₂)).1,
        MulOpposite.op (d.unop : A₁ × A₂).2 • (x : (n → A₁) × (n → A₂)).2) :=
  (rfl)

/-- The patched module is a right module over the fibre product `π₁.pullback π₂`. -/
instance instModule : Module (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) where
  one_smul x := by
    ext1
    simp only [coe_smul, MulOpposite.unop_one, OneMemClass.coe_one, Prod.fst_one, Prod.snd_one,
      MulOpposite.op_one, one_smul]
  mul_smul d e x := by
    ext1
    simp only [coe_smul, MulOpposite.unop_mul, Subring.coe_mul, Prod.fst_mul, Prod.snd_mul,
      MulOpposite.op_mul, mul_smul]
  smul_zero d := by
    ext1
    simp only [coe_smul, ZeroMemClass.coe_zero, Prod.fst_zero, Prod.snd_zero, smul_zero,
      Prod.mk_zero_zero]
  smul_add d x y := by
    ext1
    simp only [coe_smul, AddMemClass.coe_add, Prod.fst_add, Prod.snd_add, smul_add, Prod.mk_add_mk]
  add_smul d e x := by
    ext1
    simp only [coe_smul, MulOpposite.unop_add, Prod.fst_add, Prod.snd_add,
      MulOpposite.op_add, add_smul, AddMemClass.coe_add, Prod.mk_add_mk]
  zero_smul x := by
    ext1
    simp only [coe_smul, MulOpposite.unop_zero, ZeroMemClass.coe_zero, Prod.fst_zero,
      Prod.snd_zero, MulOpposite.op_zero, zero_smul, Prod.mk_zero_zero]

end patchedSubgroup

/-! ## Patched modules of the identity, of block sums and of relabelled matrices -/

variable (π₁ π₂ n) in
/-- **The patched module of the identity is free**: `M(1) ≅ Dⁿ`, sending `(a, b)` to the column
of pairs `(aᵢ, bᵢ)`, which lie in `D = π₁.pullback π₂` because `π₁(aᵢ) = π₂(bᵢ)`. -/
def patchedSubgroupOneEquiv :
    π₁.patchedSubgroup π₂ (1 : GL n Q) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] (n → (π₁.pullback π₂)ᵐᵒᵖ) where
  toFun x i := MulOpposite.op ⟨((x : (n → A₁) × (n → A₂)).1 i, (x : (n → A₁) × (n → A₂)).2 i),
    by simpa using congrFun (mem_patchedSubgroup.1 x.property) i⟩
  invFun y := ⟨(fun i ↦ ((y i).unop : A₁ × A₂).1, fun i ↦ ((y i).unop : A₁ × A₂).2), by
    rw [mem_patchedSubgroup, Units.val_one, one_mulVec]
    exact funext fun i ↦ (y i).unop.property⟩
  map_add' x y := funext fun i ↦ MulOpposite.unop_injective <| Subtype.ext <| by simp
  map_smul' d x := funext fun i ↦ MulOpposite.unop_injective <| Subtype.ext <|
    Prod.ext (by simp) (by simp)
  left_inv x := rfl
  right_inv y := rfl

@[simp]
theorem coe_unop_patchedSubgroupOneEquiv_apply (x : π₁.patchedSubgroup π₂ (1 : GL n Q)) (i : n) :
    ((patchedSubgroupOneEquiv π₁ π₂ n x i).unop : A₁ × A₂) =
      ((x : (n → A₁) × (n → A₂)).1 i, (x : (n → A₁) × (n → A₂)).2 i) :=
  (rfl)

@[simp]
theorem coe_patchedSubgroupOneEquiv_symm_apply (y : n → (π₁.pullback π₂)ᵐᵒᵖ) :
    ((patchedSubgroupOneEquiv π₁ π₂ n).symm y : (n → A₁) × (n → A₂)) =
      (fun i ↦ ((y i).unop : A₁ × A₂).1, fun i ↦ ((y i).unop : A₁ × A₂).2) :=
  (rfl)

/-- A pair of column vectors indexed by `n ⊕ m` lies in the patched module of a block diagonal
matrix `u ⊕ v` exactly when its two halves lie in `M(u)` and `M(v)`. -/
theorem mem_patchedSubgroup_fromBlocksGL {u : GL n Q} {v : GL m Q}
    {x : (n ⊕ m → A₁) × (n ⊕ m → A₂)} :
    x ∈ π₁.patchedSubgroup π₂ (fromBlocksGL (u, v)) ↔
      (x.1 ∘ Sum.inl, x.2 ∘ Sum.inl) ∈ π₁.patchedSubgroup π₂ u ∧
        (x.1 ∘ Sum.inr, x.2 ∘ Sum.inr) ∈ π₁.patchedSubgroup π₂ v := by
  simp only [mem_patchedSubgroup, coe_fromBlocksGL, fromBlocks_mulVec, zero_mulVec, add_zero,
    zero_add, Function.comp_assoc]
  constructor
  · intro h
    exact ⟨by simpa [Function.comp_assoc] using congrArg (· ∘ Sum.inl) h,
      by simpa [Function.comp_assoc] using congrArg (· ∘ Sum.inr) h⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂, ← Sum.comp_elim, Sum.elim_comp_inl_inr]

variable (π₁ π₂) in
/-- **Patched modules of block sums**: `M(u) × M(v) ≅ M(u ⊕ v)`, concatenating column vectors. -/
def patchedSubgroupProdEquiv (u : GL n Q) (v : GL m Q) :
    (π₁.patchedSubgroup π₂ u × π₁.patchedSubgroup π₂ v) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ]
      π₁.patchedSubgroup π₂ (fromBlocksGL (u, v)) where
  toFun x := ⟨(Sum.elim (x.1 : (n → A₁) × (n → A₂)).1 (x.2 : (m → A₁) × (m → A₂)).1,
      Sum.elim (x.1 : (n → A₁) × (n → A₂)).2 (x.2 : (m → A₁) × (m → A₂)).2),
    mem_patchedSubgroup_fromBlocksGL.2 ⟨x.1.property, x.2.property⟩⟩
  invFun y := (⟨_, (mem_patchedSubgroup_fromBlocksGL.1 y.property).1⟩,
    ⟨_, (mem_patchedSubgroup_fromBlocksGL.1 y.property).2⟩)
  map_add' x y := Subtype.ext <| Prod.ext (by ext (i | i) <;> simp) (by ext (i | i) <;> simp)
  map_smul' d x := Subtype.ext <| Prod.ext (by ext (i | i) <;> simp) (by ext (i | i) <;> simp)
  left_inv x := rfl
  right_inv y := Subtype.ext <| Prod.ext (Sum.elim_comp_inl_inr _) (Sum.elim_comp_inl_inr _)

@[simp]
theorem coe_patchedSubgroupProdEquiv_apply (u : GL n Q) (v : GL m Q)
    (x : π₁.patchedSubgroup π₂ u × π₁.patchedSubgroup π₂ v) :
    (patchedSubgroupProdEquiv π₁ π₂ u v x : (n ⊕ m → A₁) × (n ⊕ m → A₂)) =
      (Sum.elim (x.1 : (n → A₁) × (n → A₂)).1 (x.2 : (m → A₁) × (m → A₂)).1,
        Sum.elim (x.1 : (n → A₁) × (n → A₂)).2 (x.2 : (m → A₁) × (m → A₂)).2) :=
  (rfl)

@[simp]
theorem coe_patchedSubgroupProdEquiv_symm_apply_fst (u : GL n Q) (v : GL m Q)
    (y : π₁.patchedSubgroup π₂ (fromBlocksGL (u, v))) :
    (((patchedSubgroupProdEquiv π₁ π₂ u v).symm y).1 : (n → A₁) × (n → A₂)) =
      ((y : (n ⊕ m → A₁) × (n ⊕ m → A₂)).1 ∘ Sum.inl,
        (y : (n ⊕ m → A₁) × (n ⊕ m → A₂)).2 ∘ Sum.inl) :=
  (rfl)

@[simp]
theorem coe_patchedSubgroupProdEquiv_symm_apply_snd (u : GL n Q) (v : GL m Q)
    (y : π₁.patchedSubgroup π₂ (fromBlocksGL (u, v))) :
    (((patchedSubgroupProdEquiv π₁ π₂ u v).symm y).2 : (m → A₁) × (m → A₂)) =
      ((y : (n ⊕ m → A₁) × (n ⊕ m → A₂)).1 ∘ Sum.inr,
        (y : (n ⊕ m → A₁) × (n ⊕ m → A₂)).2 ∘ Sum.inr) :=
  (rfl)

/-- Relabelling the indices of `u` along `e : n ≃ m` relabels the patched module. -/
theorem comp_symm_mem_patchedSubgroup_reindexGL_iff (e : n ≃ m) {u : GL n Q}
    {x : (n → A₁) × (n → A₂)} :
    (x.1 ∘ e.symm, x.2 ∘ e.symm) ∈ π₁.patchedSubgroup π₂ (e.reindexGL Q u) ↔
      x ∈ π₁.patchedSubgroup π₂ u := by
  simp only [mem_patchedSubgroup, Equiv.coe_reindexGL, submatrix_mulVec_equiv, Equiv.symm_symm,
    ← Function.comp_assoc]
  simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  rw [← Function.comp_assoc π₂]
  exact e.symm.surjective.injective_comp_right.eq_iff

variable (π₁ π₂) in
/-- **Relabelling**: `M(u) ≅ M(u')` for the matrix `u'` obtained from `u` by relabelling its rows
and columns along `e : n ≃ m`. -/
def patchedSubgroupReindexEquiv (e : n ≃ m) (u : GL n Q) :
    π₁.patchedSubgroup π₂ u ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ (e.reindexGL Q u) where
  toFun x := ⟨_, (comp_symm_mem_patchedSubgroup_reindexGL_iff e).2 x.property⟩
  invFun y := ⟨((y : (m → A₁) × (m → A₂)).1 ∘ e, (y : (m → A₁) × (m → A₂)).2 ∘ e),
    (comp_symm_mem_patchedSubgroup_reindexGL_iff e).1 <| by
      simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using y.property⟩
  map_add' x y := rfl
  map_smul' d x := rfl
  left_inv x := Subtype.ext <| Prod.ext (by simp [Function.comp_assoc])
    (by simp [Function.comp_assoc])
  right_inv y := Subtype.ext <| Prod.ext (by simp [Function.comp_assoc])
    (by simp [Function.comp_assoc])

@[simp]
theorem coe_patchedSubgroupReindexEquiv_apply (e : n ≃ m) (u : GL n Q)
    (x : π₁.patchedSubgroup π₂ u) :
    (patchedSubgroupReindexEquiv π₁ π₂ e u x : (m → A₁) × (m → A₂)) =
      ((x : (n → A₁) × (n → A₂)).1 ∘ e.symm, (x : (n → A₁) × (n → A₂)).2 ∘ e.symm) :=
  (rfl)

@[simp]
theorem coe_patchedSubgroupReindexEquiv_symm_apply (e : n ≃ m) (u : GL n Q)
    (y : π₁.patchedSubgroup π₂ (e.reindexGL Q u)) :
    ((patchedSubgroupReindexEquiv π₁ π₂ e u).symm y : (n → A₁) × (n → A₂)) =
      ((y : (m → A₁) × (m → A₂)).1 ∘ e, (y : (m → A₁) × (m → A₂)).2 ∘ e) :=
  (rfl)

/-! ## Double cosets -/

/-- If `u' π₁(X₁) = π₂(X₂) u` for square matrices `X₁` over `A₁` and `X₂` over `A₂`, then
`(a, b) ↦ (X₁ a, X₂ b)` maps `M(u)` into `M(u')`. -/
theorem mulVec_mem_patchedSubgroup {u u' : GL n Q} {X₁ : Matrix n n A₁} {X₂ : Matrix n n A₂}
    (h : (u' : Matrix n n Q) * X₁.map π₁ = X₂.map π₂ * u) {x : (n → A₁) × (n → A₂)}
    (hx : x ∈ π₁.patchedSubgroup π₂ u) : (X₁ *ᵥ x.1, X₂ *ᵥ x.2) ∈ π₁.patchedSubgroup π₂ u' := by
  rw [mem_patchedSubgroup] at hx ⊢
  rw [show π₁ ∘ (X₁ *ᵥ x.1) = X₁.map π₁ *ᵥ (π₁ ∘ x.1) from funext (π₁.map_mulVec _ _),
    show π₂ ∘ (X₂ *ᵥ x.2) = X₂.map π₂ *ᵥ (π₂ ∘ x.2) from funext (π₂.map_mulVec _ _),
    mulVec_mulVec, h, ← mulVec_mulVec, hx]

/-- The matrix form of a relation `u' π₁(g₁) = π₂(g₂) u` between invertible matrices. -/
private theorem val_mul_map_eq {u u' : GL n Q} {g₁ : GL n A₁} {g₂ : GL n A₂}
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) :
    (u' : Matrix n n Q) * (g₁ : Matrix n n A₁).map π₁ = (g₂ : Matrix n n A₂).map π₂ * u := by
  simpa using congrArg Units.val h

/-- A relation `u' π₁(g₁) = π₂(g₂) u` gives the inverse relation `u π₁(g₁⁻¹) = π₂(g₂⁻¹) u'`. -/
private theorem mul_map_inv_eq {u u' : GL n Q} {g₁ : GL n A₁} {g₂ : GL n A₂}
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) :
    u * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁⁻¹ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂⁻¹ * u' := by
  rw [map_inv, map_inv, mul_inv_eq_iff_eq_mul, mul_assoc, h, inv_mul_cancel_left]

variable (π₁ π₂) in
/-- **Double coset invariance**: if `u' π₁(g₁) = π₂(g₂) u` for invertible matrices `g₁` over `A₁`
and `g₂` over `A₂`, then `(a, b) ↦ (g₁ a, g₂ b)` is an isomorphism `M(u) ≅ M(u')`. -/
def patchedSubgroupEquivOfMul {u u' : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) :
    π₁.patchedSubgroup π₂ u ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u' where
  toFun x := ⟨_, mulVec_mem_patchedSubgroup (val_mul_map_eq h) x.property⟩
  invFun y := ⟨_, mulVec_mem_patchedSubgroup (val_mul_map_eq (mul_map_inv_eq h)) y.property⟩
  map_add' x y := Subtype.ext <| Prod.ext (mulVec_add _ _ _) (mulVec_add _ _ _)
  map_smul' d x := Subtype.ext <| Prod.ext (mulVec_smul _ _ _) (mulVec_smul _ _ _)
  left_inv x := Subtype.ext <| Prod.ext (by simp [mulVec_mulVec]) (by simp [mulVec_mulVec])
  right_inv y := Subtype.ext <| Prod.ext (by simp [mulVec_mulVec]) (by simp [mulVec_mulVec])

@[simp]
theorem coe_patchedSubgroupEquivOfMul_apply {u u' : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) (x : π₁.patchedSubgroup π₂ u) :
    (patchedSubgroupEquivOfMul π₁ π₂ g₁ g₂ h x : (n → A₁) × (n → A₂)) =
      ((g₁ : Matrix n n A₁) *ᵥ (x : (n → A₁) × (n → A₂)).1,
        (g₂ : Matrix n n A₂) *ᵥ (x : (n → A₁) × (n → A₂)).2) :=
  (rfl)

@[simp]
theorem coe_patchedSubgroupEquivOfMul_symm_apply {u u' : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) (y : π₁.patchedSubgroup π₂ u') :
    ((patchedSubgroupEquivOfMul π₁ π₂ g₁ g₂ h).symm y : (n → A₁) × (n → A₂)) =
      (((g₁⁻¹ : GL n A₁) : Matrix n n A₁) *ᵥ (y : (n → A₁) × (n → A₂)).1,
        ((g₂⁻¹ : GL n A₂) : Matrix n n A₂) *ᵥ (y : (n → A₁) × (n → A₂)).2) :=
  (rfl)

/-- The patched module of an invertible matrix over `A₁`, sent to `Q`, is free. -/
theorem nonempty_patchedSubgroup_map_fst_equiv (g : GL n A₁) :
    Nonempty (π₁.patchedSubgroup π₂ (Units.map (π₁.mapMatrix (m := n)).toMonoidHom g) ≃ₗ[
      (π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ (1 : GL n Q)) :=
  ⟨patchedSubgroupEquivOfMul π₁ π₂ g 1 (by simp)⟩

/-- The patched module of an invertible matrix over `A₂`, sent to `Q`, is free. -/
theorem nonempty_patchedSubgroup_map_snd_equiv (g : GL n A₂) :
    Nonempty (π₁.patchedSubgroup π₂ (Units.map (π₂.mapMatrix (m := n)).toMonoidHom g) ≃ₗ[
      (π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ (1 : GL n Q)) :=
  ⟨patchedSubgroupEquivOfMul π₁ π₂ 1 g⁻¹ (by simp)⟩

/-- When `π₁` is surjective, right multiplication by an elementary matrix does not change the
patched module: `M(u e) ≅ M(u)`, since `e` lifts to an elementary matrix over `A₁`. -/
theorem nonempty_patchedSubgroup_mul_elementary_equiv (hπ₁ : Function.Surjective π₁)
    (u : GL n Q) {e : GL n Q} (he : e ∈ elementarySubgroup n Q) :
    Nonempty (π₁.patchedSubgroup π₂ (u * e) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u) := by
  obtain ⟨g, -, hg⟩ := π₁.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hπ₁ he
  exact ⟨patchedSubgroupEquivOfMul π₁ π₂ g 1 (by rw [hg, map_one, one_mul])⟩

/-- When `π₂` is surjective, left multiplication by an elementary matrix does not change the
patched module: `M(e u) ≅ M(u)`, since `e` lifts to an elementary matrix over `A₂`. -/
theorem nonempty_patchedSubgroup_elementary_mul_equiv (hπ₂ : Function.Surjective π₂)
    (u : GL n Q) {e : GL n Q} (he : e ∈ elementarySubgroup n Q) :
    Nonempty (π₁.patchedSubgroup π₂ (e * u) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u) := by
  obtain ⟨g, -, hg⟩ := π₂.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hπ₂ he
  exact ⟨patchedSubgroupEquivOfMul π₁ π₂ 1 g⁻¹
    (by rw [map_one, mul_one, map_inv, hg, inv_mul_cancel_left])⟩

/-- With one surjective leg, the patched module of an elementary matrix is free:
`M(e) ≅ M(1) ≅ Dⁿ`. -/
theorem nonempty_patchedSubgroup_elementary_equiv
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) {e : GL n Q}
    (he : e ∈ elementarySubgroup n Q) :
    Nonempty (π₁.patchedSubgroup π₂ e ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ]
      π₁.patchedSubgroup π₂ (1 : GL n Q)) := by
  rcases h with h | h
  · have := nonempty_patchedSubgroup_mul_elementary_equiv (π₂ := π₂) h 1 he
    rwa [one_mul] at this
  · have := nonempty_patchedSubgroup_elementary_mul_equiv (π₁ := π₁) h 1 he
    rwa [mul_one] at this

/-! ## Finite projectivity -/

/-- **`M(u) ⊕ M(u⁻¹)` is free**: with one surjective leg, `M(u) × M(u⁻¹) ≅ M(u ⊕ u⁻¹) ≅ D²ⁿ`,
because Whitehead's matrix `u ⊕ u⁻¹` is elementary. -/
theorem nonempty_patchedSubgroup_prod_inv_equiv
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) (u : GL n Q) :
    Nonempty ((π₁.patchedSubgroup π₂ u × π₁.patchedSubgroup π₂ u⁻¹) ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ]
      (n ⊕ n → (π₁.pullback π₂)ᵐᵒᵖ)) := by
  obtain ⟨e⟩ :=
    nonempty_patchedSubgroup_elementary_equiv h (fromBlocksGL_inv_mem_elementarySubgroup u)
  exact ⟨(patchedSubgroupProdEquiv π₁ π₂ u u⁻¹).trans (e.trans (patchedSubgroupOneEquiv π₁ π₂ _))⟩

/-- With one surjective leg, the patched module `M(u)` is a projective right module over the fibre
product: it is a direct summand of the free module `D²ⁿ`. -/
theorem projective_patchedSubgroup (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (u : GL n Q) : Module.Projective (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) := by
  obtain ⟨e⟩ := nonempty_patchedSubgroup_prod_inv_equiv h u
  exact .of_split (e.toLinearMap ∘ₗ LinearMap.inl _ _ _)
    (LinearMap.fst _ _ _ ∘ₗ e.symm.toLinearMap) (by ext x <;> simp)

/-- With one surjective leg, the patched module `M(u)` is a finitely generated right module over
the fibre product: it is a quotient of the free module `D²ⁿ`. -/
theorem finite_patchedSubgroup (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    (u : GL n Q) : Module.Finite (π₁.pullback π₂)ᵐᵒᵖ (π₁.patchedSubgroup π₂ u) := by
  obtain ⟨e⟩ := nonempty_patchedSubgroup_prod_inv_equiv h u
  exact .of_surjective (LinearMap.fst _ _ _ ∘ₗ e.symm.toLinearMap)
    fun x ↦ ⟨e (x, 0), by simp⟩

end RingHom
