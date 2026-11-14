/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Conj

/-!
# Isomorphisms between two objects form a torsor under automorphisms

For objects `X` and `Y` of a category, the automorphism group `Aut Y` acts on the isomorphisms
`X ≅ Y` by postcomposition. As in the group structure of `Aut Y`, whose multiplication agrees with
function composition, `σ • e` is `e` followed by `σ`, so this is a left action. It is free and
transitive: for isomorphisms `e₁ e₂ : X ≅ Y` the automorphism `e₁.symm ≪≫ e₂` of `Y` is the unique
automorphism carrying `e₁` to `e₂` (`CategoryTheory.Iso.existsUnique_smul_eq`). When `X` and `Y`
are isomorphic, `X ≅ Y` is therefore a torsor under `Aut Y` (`CategoryTheory.Aut.instTorsorIso`).

Symmetrically, `(Aut X)ᵐᵒᵖ` acts on `X ≅ Y` by precomposition, `op σ • e = σ ≪≫ e`; this action
commutes with the action of `Aut Y` and is also simply transitive
(`CategoryTheory.Iso.existsUnique_op_smul_eq`).

Conjugation by an isomorphism `e : X ≅ Y`, which identifies `Aut X` with `Aut Y`, is compatible
with these actions: `e.conjAut σ` acts on `e` as `σ` acts on `e` by precomposition
(`CategoryTheory.Iso.conjAut_smul`).

For the geometric fibre functors of a Galois category, these isomorphisms are the paths between
base points, and these are the simply transitive actions of the fundamental groups at the two
endpoints on paths.

## Main definitions

* `CategoryTheory.Aut.instMulActionIso`: the action of `Aut Y` on `X ≅ Y` by postcomposition.
* `CategoryTheory.Aut.instTorsorIso`: if `X ≅ Y` is nonempty, it is a torsor under `Aut Y`.
* `CategoryTheory.Aut.instMulActionOpIso`: the action of `(Aut X)ᵐᵒᵖ` on `X ≅ Y` by
  precomposition.

## Main results

* `CategoryTheory.Iso.existsUnique_smul_eq`: the action of `Aut Y` on `X ≅ Y` is simply
  transitive.
* `CategoryTheory.Iso.existsUnique_op_smul_eq`: the action of `(Aut X)ᵐᵒᵖ` on `X ≅ Y` is simply
  transitive.
* `CategoryTheory.Iso.conjAut_smul`: conjugation by `e` is compatible with the actions on `e`.
-/

public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C}

namespace Aut

/-! ### Postcomposition by `Aut Y` -/

/-- The automorphism group `Aut Y` acts on isomorphisms `X ≅ Y` by postcomposition: `σ • e` is
`e` followed by `σ`. -/
instance instSMulIso : SMul (Aut Y) (X ≅ Y) where
  smul σ e := e ≪≫ σ.asIso

theorem smul_iso_def (σ : Aut Y) (e : X ≅ Y) : σ • e = e ≪≫ σ.asIso :=
  rfl

@[simp]
theorem smul_iso_hom (σ : Aut Y) (e : X ≅ Y) : (σ • e).hom = e.hom ≫ σ.asIso.hom :=
  rfl

@[simp]
theorem smul_iso_inv (σ : Aut Y) (e : X ≅ Y) : (σ • e).inv = σ.asIso.inv ≫ e.inv :=
  rfl

/-- Postcomposition is a left action of `Aut Y` on `X ≅ Y`, because the multiplication of `Aut Y`
agrees with function composition. -/
instance instMulActionIso : MulAction (Aut Y) (X ≅ Y) where
  one_smul e := by ext; simp
  mul_smul σ τ e := by ext; simp

/-- The automorphism `e₁ /ₛ e₂` of `Y` carrying `e₂` to `e₁`, namely `e₂.symm ≪≫ e₁`. -/
instance instSDivIso : SDiv (Aut Y) (X ≅ Y) where
  sdiv e₁ e₂ := .of (e₂.symm ≪≫ e₁)

theorem sdiv_iso_def (e₁ e₂ : X ≅ Y) : (e₁ /ₛ e₂ : Aut Y) = .of (e₂.symm ≪≫ e₁) :=
  rfl

@[simp]
theorem sdiv_iso_asIso (e₁ e₂ : X ≅ Y) : (e₁ /ₛ e₂ : Aut Y).asIso = e₂.symm ≪≫ e₁ :=
  rfl

@[simp]
theorem sdiv_smul_iso (e₁ e₂ : X ≅ Y) : (e₁ /ₛ e₂ : Aut Y) • e₂ = e₁ := by
  ext; simp

@[simp]
theorem smul_sdiv_iso (σ : Aut Y) (e : X ≅ Y) : (σ • e) /ₛ e = σ := by
  ext1; ext; simp

/-- **When `X` and `Y` are isomorphic, `X ≅ Y` is a torsor under `Aut Y`**, acting by
postcomposition. -/
instance instTorsorIso [Nonempty (X ≅ Y)] : Torsor (Aut Y) (X ≅ Y) where
  toMulAction := instMulActionIso
  toSDiv := instSDivIso
  sdiv_smul' := sdiv_smul_iso
  smul_sdiv' := smul_sdiv_iso

instance : MulAction.IsPretransitive (Aut Y) (X ≅ Y) :=
  ⟨fun e₁ e₂ ↦ ⟨e₂ /ₛ e₁, sdiv_smul_iso e₂ e₁⟩⟩

/-! ### Precomposition by `Aut X` -/

/-- The opposite of the automorphism group `Aut X` acts on isomorphisms `X ≅ Y` by
precomposition: `op σ • e` is `σ` followed by `e`. -/
instance instSMulOpIso : SMul (Aut X)ᵐᵒᵖ (X ≅ Y) where
  smul σ e := σ.unop.asIso ≪≫ e

theorem op_smul_iso_def (σ : (Aut X)ᵐᵒᵖ) (e : X ≅ Y) : σ • e = σ.unop.asIso ≪≫ e :=
  rfl

@[simp]
theorem op_smul_iso_hom (σ : (Aut X)ᵐᵒᵖ) (e : X ≅ Y) : (σ • e).hom = σ.unop.asIso.hom ≫ e.hom :=
  rfl

@[simp]
theorem op_smul_iso_inv (σ : (Aut X)ᵐᵒᵖ) (e : X ≅ Y) : (σ • e).inv = e.inv ≫ σ.unop.asIso.inv :=
  rfl

/-- Precomposition is a left action of `(Aut X)ᵐᵒᵖ` on `X ≅ Y`. -/
instance instMulActionOpIso : MulAction (Aut X)ᵐᵒᵖ (X ≅ Y) where
  one_smul e := by ext; simp
  mul_smul σ τ e := by ext; simp

instance : SMulCommClass (Aut Y) (Aut X)ᵐᵒᵖ (X ≅ Y) where
  smul_comm σ τ e := by ext; simp

instance : SMulCommClass (Aut X)ᵐᵒᵖ (Aut Y) (X ≅ Y) :=
  .symm _ _ _

instance : MulAction.IsPretransitive (Aut X)ᵐᵒᵖ (X ≅ Y) :=
  ⟨fun e₁ e₂ ↦ ⟨.op (.of (e₂ ≪≫ e₁.symm)), by ext; simp⟩⟩

end Aut

namespace Iso

/-- **The action of `Aut Y` on `X ≅ Y` is simply transitive**: any two isomorphisms `X ≅ Y` differ
by a unique automorphism of `Y`. -/
theorem existsUnique_smul_eq (e₁ e₂ : X ≅ Y) : ∃! σ : Aut Y, σ • e₁ = e₂ := by
  refine ⟨e₂ /ₛ e₁, Aut.sdiv_smul_iso e₂ e₁, fun σ h ↦ ?_⟩
  rw [← h, Aut.smul_sdiv_iso]

/-- **The action of `(Aut X)ᵐᵒᵖ` on `X ≅ Y` is simply transitive**: any two isomorphisms `X ≅ Y`
differ by a unique automorphism of `X`. -/
theorem existsUnique_op_smul_eq (e₁ e₂ : X ≅ Y) :
    ∃! σ : Aut X, MulOpposite.op σ • e₁ = e₂ := by
  refine ⟨.of (e₂ ≪≫ e₁.symm), by ext; simp, fun σ h ↦ ?_⟩
  ext1
  ext
  simp [← h]

/-- Conjugation by `e : X ≅ Y` is compatible with the actions on `e`: the automorphism
`e.conjAut σ` of `Y` acts on `e` by postcomposition as the automorphism `σ` of `X` acts on `e` by
precomposition. -/
theorem conjAut_smul (e : X ≅ Y) (σ : Aut X) : e.conjAut σ • e = MulOpposite.op σ • e := by
  ext
  simp [Iso.conjAut_apply]

end Iso

end CategoryTheory
