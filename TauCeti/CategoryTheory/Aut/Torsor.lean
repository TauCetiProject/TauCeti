/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.Conj

/-!
# Isomorphisms between two objects form a torsor under automorphisms

For objects `X` and `Y` of a category, the automorphism group `Aut Y` acts on the isomorphisms
`X ≅ Y` by postcomposition. As in the group structure of `Aut Y`, whose multiplication agrees with
function composition, `σ • e` is `e` followed by `σ`, so this is a left action. It is free and
transitive: for isomorphisms `e₁ e₂ : X ≅ Y` the automorphism `e₂.symm ≪≫ e₁` of `Y` is the unique
automorphism carrying `e₂` to `e₁` (`CategoryTheory.Aut.existsUnique_smul_eq`). When `X` and `Y`
are isomorphic, `X ≅ Y` is therefore a torsor under `Aut Y` (`CategoryTheory.Aut.instTorsorIso`).

Conjugation by an isomorphism `e : X ≅ Y`, which identifies `Aut X` with `Aut Y`, is compatible
with this action: `e.conjAut σ` acts on `e` as `σ` acts on `e` by precomposition
(`CategoryTheory.Aut.conjAut_smul`).

For the geometric fibre functors of a Galois category, these isomorphisms are the paths between
base points, and this is the simply transitive action of a fundamental group on paths.

## Main definitions

* `CategoryTheory.Aut.instMulActionIso`: the action of `Aut Y` on `X ≅ Y` by postcomposition.
* `CategoryTheory.Aut.instTorsorIso`: if `X ≅ Y` is nonempty, it is a torsor under `Aut Y`.

## Main results

* `CategoryTheory.Aut.existsUnique_smul_eq`: the action of `Aut Y` on `X ≅ Y` is simply
  transitive.
* `CategoryTheory.Aut.conjAut_smul`: conjugation by `e` is compatible with the action on `e`.
-/

public section

namespace CategoryTheory.Aut

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- The automorphism group `Aut Y` acts on isomorphisms `X ≅ Y` by postcomposition: `σ • e` is
`e` followed by `σ`. -/
instance instSMulIso : SMul (Aut Y) (X ≅ Y) where
  smul σ e := e ≪≫ σ.asIso

@[simp]
theorem smul_iso (σ : Aut Y) (e : X ≅ Y) : σ • e = e ≪≫ σ.asIso :=
  rfl

/-- Postcomposition is a left action of `Aut Y` on `X ≅ Y`, because the multiplication of `Aut Y`
agrees with function composition. -/
instance instMulActionIso : MulAction (Aut Y) (X ≅ Y) where
  one_smul e := by simp
  mul_smul σ τ e := by simp

/-- The automorphism `e₁ /ₛ e₂` of `Y` carrying `e₂` to `e₁`, namely `e₂.symm ≪≫ e₁`. -/
instance instSDivIso : SDiv (Aut Y) (X ≅ Y) where
  sdiv e₁ e₂ := .of (e₂.symm ≪≫ e₁)

@[simp]
theorem sdiv_iso_asIso (e₁ e₂ : X ≅ Y) : (e₁ /ₛ e₂ : Aut Y).asIso = e₂.symm ≪≫ e₁ :=
  rfl

/-- **The action of `Aut Y` on `X ≅ Y` is simply transitive**: any two isomorphisms `X ≅ Y` differ
by a unique automorphism of `Y`. -/
theorem existsUnique_smul_eq (e₁ e₂ : X ≅ Y) : ∃! σ : Aut Y, σ • e₂ = e₁ := by
  refine ⟨e₁ /ₛ e₂, by simp, fun σ h ↦ ?_⟩
  ext1
  simp [← h]

/-- **When `X` and `Y` are isomorphic, `X ≅ Y` is a torsor under `Aut Y`**, acting by
postcomposition. -/
instance instTorsorIso [Nonempty (X ≅ Y)] : Torsor (Aut Y) (X ≅ Y) where
  toMulAction := instMulActionIso
  toSDiv := instSDivIso
  sdiv_smul' e₁ e₂ := by simp
  smul_sdiv' σ e := by
    ext1
    simp

/-- Conjugation by `e : X ≅ Y` is compatible with the action on `e`: the automorphism
`e.conjAut σ` of `Y` acts on `e` as the automorphism `σ` of `X` acts on `e` by precomposition. -/
theorem conjAut_smul (e : X ≅ Y) (σ : Aut X) : e.conjAut σ • e = σ.asIso ≪≫ e := by
  simp [Iso.conjAut_apply]

end CategoryTheory.Aut
