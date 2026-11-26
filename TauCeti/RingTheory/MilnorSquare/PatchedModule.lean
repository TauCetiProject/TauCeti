/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
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

Matrices `X₁` over `A₁` and `X₂` over `A₂` with `u' π₁(X₁) = π₂(X₂) u` induce the linear map
`(a, b) ↦ (X₁ a, X₂ b)` from `M(u)` to `M(u')`. With one surjective leg, every linear map between
patched modules arises in this way from a unique pair of matrices: `M(u)` is a retract of
`M(1) ≅ D²ⁿ` by maps of this form, and a linear map out of `M(1)` is determined by the images of
the standard basis vectors. Consequently the converse of the double coset invariance holds:
`M(u) ≅ M(u')` exactly when `u' π₁(g₁) = π₂(g₂) u` for invertible matrices `g₁` and `g₂`. This is
the matrix form of the full faithfulness in Milnor's patching theorem, and it gives the exactness
of the Mayer–Vietoris sequence at `K₁(Q)`.

## Main definitions

* `RingHom.patchedSubgroup π₁ π₂ u`: the patched module `M(u)`, an additive subgroup of
  `A₁ⁿ × A₂ⁿ` with its right `D`-module structure.
* `RingHom.patchedSubgroupLinearMap π₁ π₂ X₁ X₂ h`: the linear map `M(u) → M(u')`,
  `(a, b) ↦ (X₁ a, X₂ b)`, induced by a compatible pair of matrices.

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
* `RingHom.exists_patchedSubgroupLinearMap_eq`, `RingHom.patchedSubgroupLinearMap_inj`: with one
  surjective leg, every linear map between patched modules is induced by a unique pair of matrices.
* `RingHom.nonempty_patchedSubgroup_equiv_iff`: with one surjective leg, `M(u) ≅ M(u')` if and only
  if `u` and `u'` lie in the same double coset of the images of `GLₙ(A₂)` and `GLₙ(A₁)`.

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
    Prod.ext (by simp [patchedSubgroup.coe_smul]) (by simp [patchedSubgroup.coe_smul])
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
  map_smul' d x := Subtype.ext <| Prod.ext (by ext (i | i) <;> simp [patchedSubgroup.coe_smul])
    (by ext (i | i) <;> simp [patchedSubgroup.coe_smul])
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

/-! ## Linear maps induced by matrices -/

/-- If `u' π₁(X₁) = π₂(X₂) u` for (possibly rectangular) matrices `X₁` over `A₁` and `X₂` over
`A₂`, then `(a, b) ↦ (X₁ a, X₂ b)` maps `M(u)` into `M(u')`. -/
theorem mulVec_mem_patchedSubgroup {u : GL n Q} {u' : GL m Q} {X₁ : Matrix m n A₁}
    {X₂ : Matrix m n A₂} (h : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q))
    {x : (n → A₁) × (n → A₂)} (hx : x ∈ π₁.patchedSubgroup π₂ u) :
    (X₁ *ᵥ x.1, X₂ *ᵥ x.2) ∈ π₁.patchedSubgroup π₂ u' := by
  rw [mem_patchedSubgroup] at hx ⊢
  rw [show π₁ ∘ (X₁ *ᵥ x.1) = X₁.map π₁ *ᵥ (π₁ ∘ x.1) from funext (π₁.map_mulVec _ _),
    show π₂ ∘ (X₂ *ᵥ x.2) = X₂.map π₂ *ᵥ (π₂ ∘ x.2) from funext (π₂.map_mulVec _ _),
    mulVec_mulVec, h, ← mulVec_mulVec, hx]

variable (π₁ π₂) in
/-- The linear map `M(u) → M(u')`, `(a, b) ↦ (X₁ a, X₂ b)`, induced by matrices `X₁` over `A₁` and
`X₂` over `A₂` with `u' π₁(X₁) = π₂(X₂) u`. With one surjective leg every linear map between
patched modules is of this form (`RingHom.exists_patchedSubgroupLinearMap_eq`), for a unique pair
of matrices (`RingHom.patchedSubgroupLinearMap_inj`). -/
def patchedSubgroupLinearMap {u : GL n Q} {u' : GL m Q} (X₁ : Matrix m n A₁) (X₂ : Matrix m n A₂)
    (h : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q)) :
    π₁.patchedSubgroup π₂ u →ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u' where
  toFun x := ⟨_, mulVec_mem_patchedSubgroup h x.property⟩
  map_add' _ _ := Subtype.ext <| Prod.ext (mulVec_add _ _ _) (mulVec_add _ _ _)
  map_smul' _ _ := Subtype.ext <| Prod.ext (mulVec_smul _ _ _) (mulVec_smul _ _ _)

@[simp]
theorem coe_patchedSubgroupLinearMap_apply {u : GL n Q} {u' : GL m Q} (X₁ : Matrix m n A₁)
    (X₂ : Matrix m n A₂) (h : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q))
    (x : π₁.patchedSubgroup π₂ u) :
    (patchedSubgroupLinearMap π₁ π₂ X₁ X₂ h x : (m → A₁) × (m → A₂)) =
      (X₁ *ᵥ (x : (n → A₁) × (n → A₂)).1, X₂ *ᵥ (x : (n → A₁) × (n → A₂)).2) :=
  (rfl)

/-- The identity matrices induce the identity of `M(u)`. -/
@[simp]
theorem patchedSubgroupLinearMap_one {u : GL n Q}
    (h : (u : Matrix n n Q) * (1 : Matrix n n A₁).map π₁ =
      (1 : Matrix n n A₂).map π₂ * (u : Matrix n n Q)) :
    patchedSubgroupLinearMap π₁ π₂ 1 1 h = LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp

/-- The composite of the maps induced by two pairs of matrices is induced by their products. -/
@[simp]
theorem patchedSubgroupLinearMap_comp {k : Type*} [Fintype k] [DecidableEq k] {u : GL n Q}
    {u' : GL m Q} {u'' : GL k Q} (Y₁ : Matrix k m A₁) (Y₂ : Matrix k m A₂)
    (hY : (u'' : Matrix k k Q) * Y₁.map π₁ = Y₂.map π₂ * (u' : Matrix m m Q)) (X₁ : Matrix m n A₁)
    (X₂ : Matrix m n A₂) (hX : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q)) :
    patchedSubgroupLinearMap π₁ π₂ Y₁ Y₂ hY ∘ₗ patchedSubgroupLinearMap π₁ π₂ X₁ X₂ hX =
      patchedSubgroupLinearMap π₁ π₂ (Y₁ * X₁) (Y₂ * X₂) (by
        rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mul_assoc, hY, Matrix.mul_assoc, hX,
          Matrix.mul_assoc]) :=
  LinearMap.ext fun x ↦ Subtype.ext <| by simp [mulVec_mulVec]

/-! ## Double cosets -/

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
    π₁.patchedSubgroup π₂ u ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u' :=
  .ofLinearMap (patchedSubgroupLinearMap π₁ π₂ _ _ (val_mul_map_eq h))
    (patchedSubgroupLinearMap π₁ π₂ _ _ (val_mul_map_eq (mul_map_inv_eq h)))
    (by simp) (by simp)

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

/-- The isomorphism `M(u) ≅ M(u')` given by invertible matrices `g₁` and `g₂` is the linear map
induced by these matrices. -/
@[simp]
theorem patchedSubgroupEquivOfMul_toLinearMap {u u' : GL n Q} (g₁ : GL n A₁) (g₂ : GL n A₂)
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) :
    (patchedSubgroupEquivOfMul π₁ π₂ g₁ g₂ h).toLinearMap =
      patchedSubgroupLinearMap π₁ π₂ (g₁ : Matrix n n A₁) (g₂ : Matrix n n A₂)
        (by simpa using congrArg Units.val h) :=
  (rfl)

/-- The inverse of the isomorphism `M(u) ≅ M(u')` given by invertible matrices `g₁` and `g₂` is
the linear map induced by `g₁⁻¹` and `g₂⁻¹`. -/
@[simp]
theorem patchedSubgroupEquivOfMul_symm_toLinearMap {u u' : GL n Q} (g₁ : GL n A₁)
    (g₂ : GL n A₂)
    (h : u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
      Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u) :
    (patchedSubgroupEquivOfMul π₁ π₂ g₁ g₂ h).symm.toLinearMap =
      patchedSubgroupLinearMap π₁ π₂ ((g₁⁻¹ : GL n A₁) : Matrix n n A₁)
        ((g₂⁻¹ : GL n A₂) : Matrix n n A₂) (by simpa using congrArg Units.val (mul_map_inv_eq h)) :=
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

/-! ## Linear maps between patched modules

With one surjective leg, every linear map `M(u) → M(u')` is the map `(a, b) ↦ (X₁ a, X₂ b)` induced
by a unique pair of matrices `X₁` over `A₁` and `X₂` over `A₂` with `u' π₁(X₁) = π₂(X₂) u`. The
proof writes `M(u)` as a retract of `M(1) ≅ D²ⁿ` by maps given by matrices, using an invertible lift
of Whitehead's matrix `u ⊕ u⁻¹`. -/

section LinearMap

/-- The image of the standard basis vector `eᵢ` of `Dⁿ` in `M(1)` is the pair `(eᵢ, eᵢ)`. -/
private theorem coe_patchedSubgroupOneEquiv_symm_single (i : n) :
    ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1) : (n → A₁) × (n → A₂)) =
      (Pi.single i 1, Pi.single i 1) := by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun j ↦ ?_) <;>
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

/-- Two linear maps out of `M(1) ≅ Dⁿ` agreeing on the standard basis vectors are equal. -/
private theorem linearMap_patchedSubgroup_one_ext {M : Type*} [AddCommGroup M]
    [Module (π₁.pullback π₂)ᵐᵒᵖ M]
    {f g : π₁.patchedSubgroup π₂ (1 : GL n Q) →ₗ[(π₁.pullback π₂)ᵐᵒᵖ] M}
    (h : ∀ i, f ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1)) =
      g ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1))) : f = g :=
  ((Pi.basisFun (π₁.pullback π₂)ᵐᵒᵖ n).map (patchedSubgroupOneEquiv π₁ π₂ n).symm).ext
    fun i ↦ by simpa using h i

/-- Every linear map out of `M(1) ≅ Dⁿ` is induced by matrices: their columns are the images of
the standard basis vectors. -/
private theorem exists_patchedSubgroupLinearMap_eq_of_one {u' : GL m Q}
    (f : π₁.patchedSubgroup π₂ (1 : GL n Q) →ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u') :
    ∃ (X₁ : Matrix m n A₁) (X₂ : Matrix m n A₂)
      (h : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * ((1 : GL n Q) : Matrix n n Q)),
      patchedSubgroupLinearMap π₁ π₂ X₁ X₂ h = f := by
  let X₁ : Matrix m n A₁ :=
    .of fun r i ↦ (↑(f ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1))) :
      (m → A₁) × (m → A₂)).1 r
  let X₂ : Matrix m n A₂ :=
    .of fun r i ↦ (↑(f ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1))) :
      (m → A₁) × (m → A₂)).2 r
  have hcol (i : n) : (X₁ *ᵥ Pi.single i 1, X₂ *ᵥ Pi.single i 1) =
      (f ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1)) : (m → A₁) × (m → A₂)) := by
    refine Prod.ext (funext fun r ↦ ?_) (funext fun r ↦ ?_) <;> simp [X₁, X₂]
  have h : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * ((1 : GL n Q) : Matrix n n Q) := by
    refine ext_of_mulVec_single fun i ↦ ?_
    have hmem := (f ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1))).property
    rw [← hcol, mem_patchedSubgroup] at hmem
    simpa [mulVec_single_one, col_mul_eq_mulVec_col, col_map] using hmem
  exact ⟨X₁, X₂, h, linearMap_patchedSubgroup_one_ext fun i ↦ Subtype.ext <| by
    rw [coe_patchedSubgroupLinearMap_apply, coe_patchedSubgroupOneEquiv_symm_single]
    exact hcol i⟩

/-- The images of a lift `X` of Whitehead's matrix `u ⊕ u⁻¹` and of its inverse, as block
matrices. -/
private theorem map_val_eq_fromBlocks {A : Type*} [Ring A] (π : A →+* Q) {u : GL n Q}
    {X : GL (n ⊕ n) A}
    (hX : Units.map (π.mapMatrix (m := n ⊕ n)).toMonoidHom X = fromBlocksGL (u, u⁻¹)) :
    (X : Matrix (n ⊕ n) (n ⊕ n) A).map π = fromBlocks u 0 0 ↑u⁻¹ ∧
      ((X⁻¹ : GL (n ⊕ n) A) : Matrix (n ⊕ n) (n ⊕ n) A).map π = fromBlocks ↑u⁻¹ 0 0 u := by
  have hinv := congrArg Inv.inv hX
  rw [← map_inv, ← map_inv, Prod.inv_mk, inv_inv] at hinv
  exact ⟨by simpa using congrArg Units.val hX, by simpa using congrArg Units.val hinv⟩

/-- With one surjective leg, `M(u)` is a retract of `M(1) ≅ D²ⁿ` by maps given by matrices: there
are matrix pairs `(I₁, I₂)` inducing `M(u) → M(1)` and `(R₁, R₂)` inducing `M(1) → M(u)` with
`R₁ I₁ = 1` and `R₂ I₂ = 1`. They are built from an invertible lift `X` of `u ⊕ u⁻¹` along the
surjective leg: for `π₁` surjective, `I₁ = X J`, `I₂ = J`, `R₁ = Jᵀ X⁻¹` and `R₂ = Jᵀ`, where `J` is
the inclusion of the first block. -/
private theorem exists_patchedSubgroup_retract
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) (u : GL n Q) :
    ∃ (I₁ : Matrix (n ⊕ n) n A₁) (I₂ : Matrix (n ⊕ n) n A₂) (R₁ : Matrix n (n ⊕ n) A₁)
      (R₂ : Matrix n (n ⊕ n) A₂),
      ((1 : GL (n ⊕ n) Q) : Matrix (n ⊕ n) (n ⊕ n) Q) * I₁.map π₁ = I₂.map π₂ * (u : Matrix n n Q) ∧
      (u : Matrix n n Q) * R₁.map π₁ =
        R₂.map π₂ * ((1 : GL (n ⊕ n) Q) : Matrix (n ⊕ n) (n ⊕ n) Q) ∧
      R₁ * I₁ = 1 ∧ R₂ * I₂ = 1 := by
  have hW := fromBlocksGL_inv_mem_elementarySubgroup u
  rcases h with h | h
  · obtain ⟨X, -, hX⟩ := π₁.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq h hW
    obtain ⟨hX₁, hX₂⟩ := map_val_eq_fromBlocks π₁ hX
    refine ⟨(X : Matrix (n ⊕ n) (n ⊕ n) A₁) * fromRows 1 0, fromRows 1 0,
      fromCols 1 0 * ((X⁻¹ : GL (n ⊕ n) A₁) : Matrix (n ⊕ n) (n ⊕ n) A₁), fromCols 1 0,
      ?_, ?_, ?_, ?_⟩
    · simp [Matrix.map_mul, hX₁, fromRows_map, fromBlocks_mul_fromRows, fromRows_mul]
    · simp [Matrix.map_mul, hX₂, fromCols_map, fromCols_mul_fromBlocks, mul_fromCols]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (X : Matrix (n ⊕ n) (n ⊕ n) A₁), Units.inv_mul,
        Matrix.one_mul]
      simp [fromCols_mul_fromRows]
    · simp [fromCols_mul_fromRows]
  · obtain ⟨Y, -, hY⟩ := π₂.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq h hW
    obtain ⟨hY₁, hY₂⟩ := map_val_eq_fromBlocks π₂ hY
    refine ⟨fromRows 1 0, ((Y⁻¹ : GL (n ⊕ n) A₂) : Matrix (n ⊕ n) (n ⊕ n) A₂) * fromRows 1 0,
      fromCols 1 0, fromCols 1 0 * (Y : Matrix (n ⊕ n) (n ⊕ n) A₂), ?_, ?_, ?_, ?_⟩
    · simp [Matrix.map_mul, hY₂, fromRows_map, fromBlocks_mul_fromRows, fromRows_mul]
    · simp [Matrix.map_mul, hY₁, fromCols_map, fromCols_mul_fromBlocks, mul_fromCols]
    · simp [fromCols_mul_fromRows]
    · rw [Matrix.mul_assoc,
        ← Matrix.mul_assoc _ ((Y⁻¹ : GL (n ⊕ n) A₂) : Matrix (n ⊕ n) (n ⊕ n) A₂), Units.mul_inv,
        Matrix.one_mul]
      simp [fromCols_mul_fromRows]

/-- The matrices inducing a linear map out of `M(1) ≅ Dⁿ` are unique: their columns are the images
of the standard basis vectors. -/
private theorem eq_of_patchedSubgroupLinearMap_one_eq {u' : GL m Q} {X₁ Y₁ : Matrix m n A₁}
    {X₂ Y₂ : Matrix m n A₂}
    (hX : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * ((1 : GL n Q) : Matrix n n Q))
    (hY : (u' : Matrix m m Q) * Y₁.map π₁ = Y₂.map π₂ * ((1 : GL n Q) : Matrix n n Q))
    (e : patchedSubgroupLinearMap π₁ π₂ X₁ X₂ hX = patchedSubgroupLinearMap π₁ π₂ Y₁ Y₂ hY) :
    X₁ = Y₁ ∧ X₂ = Y₂ := by
  have he (i : n) := congrArg Subtype.val
    (LinearMap.congr_fun e ((patchedSubgroupOneEquiv π₁ π₂ n).symm (Pi.single i 1)))
  simp only [coe_patchedSubgroupLinearMap_apply, coe_patchedSubgroupOneEquiv_symm_single,
    Prod.mk.injEq] at he
  exact ⟨ext_of_mulVec_single fun i ↦ (he i).1, ext_of_mulVec_single fun i ↦ (he i).2⟩

/-- With one surjective leg, the matrices inducing a linear map between patched modules are
unique. -/
theorem patchedSubgroupLinearMap_inj (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {u : GL n Q} {u' : GL m Q} {X₁ Y₁ : Matrix m n A₁} {X₂ Y₂ : Matrix m n A₂}
    (hX : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q))
    (hY : (u' : Matrix m m Q) * Y₁.map π₁ = Y₂.map π₂ * (u : Matrix n n Q)) :
    patchedSubgroupLinearMap π₁ π₂ X₁ X₂ hX = patchedSubgroupLinearMap π₁ π₂ Y₁ Y₂ hY ↔
      X₁ = Y₁ ∧ X₂ = Y₂ := by
  refine ⟨fun e ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by subst h₁ h₂; rfl⟩
  -- Compose with the retraction `M(1) → M(u)` given by `(R₁, R₂)`, then cancel `R I = 1`.
  obtain ⟨I₁, I₂, R₁, R₂, -, hR, hRI₁, hRI₂⟩ := exists_patchedSubgroup_retract h u
  have e' := congrArg (· ∘ₗ patchedSubgroupLinearMap π₁ π₂ R₁ R₂ hR) e
  simp only [patchedSubgroupLinearMap_comp] at e'
  obtain ⟨e₁, e₂⟩ := eq_of_patchedSubgroupLinearMap_one_eq _ _ e'
  exact ⟨by simpa [Matrix.mul_assoc, hRI₁] using congrArg (· * I₁) e₁,
    by simpa [Matrix.mul_assoc, hRI₂] using congrArg (· * I₂) e₂⟩

/-- **Linear maps between patched modules are given by matrices.** With one surjective leg, every
linear map `f : M(u) → M(u')` of right modules over the fibre product is `(a, b) ↦ (X₁ a, X₂ b)`
for matrices `X₁` over `A₁` and `X₂` over `A₂` with `u' π₁(X₁) = π₂(X₂) u`. -/
theorem exists_patchedSubgroupLinearMap_eq (h : Function.Surjective π₁ ∨ Function.Surjective π₂)
    {u : GL n Q} {u' : GL m Q}
    (f : π₁.patchedSubgroup π₂ u →ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u') :
    ∃ (X₁ : Matrix m n A₁) (X₂ : Matrix m n A₂)
      (hX : (u' : Matrix m m Q) * X₁.map π₁ = X₂.map π₂ * (u : Matrix n n Q)),
      patchedSubgroupLinearMap π₁ π₂ X₁ X₂ hX = f := by
  obtain ⟨I₁, I₂, R₁, R₂, hI, hR, hRI₁, hRI₂⟩ := exists_patchedSubgroup_retract h u
  obtain ⟨G₁, G₂, hG, hGf⟩ :=
    exists_patchedSubgroupLinearMap_eq_of_one (f ∘ₗ patchedSubgroupLinearMap π₁ π₂ R₁ R₂ hR)
  refine ⟨_, _, _, (patchedSubgroupLinearMap_comp G₁ G₂ hG I₁ I₂ hI).symm.trans ?_⟩
  rw [hGf, LinearMap.comp_assoc, patchedSubgroupLinearMap_comp]
  simp only [hRI₁, hRI₂, patchedSubgroupLinearMap_one, LinearMap.comp_id]

/-- **The patched module determines the double coset.** With one surjective leg, `M(u) ≅ M(u')`
for `u, u' ∈ GLₙ(Q)` if and only if `u' π₁(g₁) = π₂(g₂) u` for invertible matrices `g₁` over `A₁`
and `g₂` over `A₂`, that is, if `u` and `u'` lie in the same double coset of the images of
`GLₙ(A₂)` and `GLₙ(A₁)`. -/
theorem nonempty_patchedSubgroup_equiv_iff
    (h : Function.Surjective π₁ ∨ Function.Surjective π₂) {u u' : GL n Q} :
    Nonempty (π₁.patchedSubgroup π₂ u ≃ₗ[(π₁.pullback π₂)ᵐᵒᵖ] π₁.patchedSubgroup π₂ u') ↔
      ∃ (g₁ : GL n A₁) (g₂ : GL n A₂),
        u' * Units.map (π₁.mapMatrix (m := n)).toMonoidHom g₁ =
          Units.map (π₂.mapMatrix (m := n)).toMonoidHom g₂ * u := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨g₁, g₂, hg⟩ ↦ ⟨patchedSubgroupEquivOfMul π₁ π₂ g₁ g₂ hg⟩⟩
  obtain ⟨X₁, X₂, hX, hXe⟩ := exists_patchedSubgroupLinearMap_eq h e.toLinearMap
  obtain ⟨Y₁, Y₂, hY, hYe⟩ := exists_patchedSubgroupLinearMap_eq h e.symm.toLinearMap
  have h₁ : (u : Matrix n n Q) * (1 : Matrix n n A₁).map π₁ =
      (1 : Matrix n n A₂).map π₂ * (u : Matrix n n Q) := by simp
  have h₁' : (u' : Matrix n n Q) * (1 : Matrix n n A₁).map π₁ =
      (1 : Matrix n n A₂).map π₂ * (u' : Matrix n n Q) := by simp
  -- The composites `e⁻¹ ∘ e` and `e ∘ e⁻¹` are the identities, so the matrices are inverse.
  have hYX := (patchedSubgroupLinearMap_inj h _ h₁).1 <| by
    rw [← patchedSubgroupLinearMap_comp Y₁ Y₂ hY X₁ X₂ hX, hXe, hYe, patchedSubgroupLinearMap_one]
    exact e.symm_comp
  have hXY := (patchedSubgroupLinearMap_inj h _ h₁').1 <| by
    rw [← patchedSubgroupLinearMap_comp X₁ X₂ hX Y₁ Y₂ hY, hXe, hYe, patchedSubgroupLinearMap_one]
    exact e.comp_symm
  exact ⟨⟨X₁, Y₁, hXY.1, hYX.1⟩, ⟨X₂, Y₂, hXY.2, hYX.2⟩, Units.ext (by simpa using hX)⟩

end LinearMap

end RingHom
