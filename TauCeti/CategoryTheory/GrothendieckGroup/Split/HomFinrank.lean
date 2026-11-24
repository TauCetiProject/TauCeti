/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import TauCeti.CategoryTheory.Linear.Biproduct
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Hom ranks on split `K₀` of a linear category

Let `C` be a `k`-linear category with binary biproducts and `σ` an object of `C` whose Hom
modules `σ ⟶ X` are finite and free, for instance any object of a category of finite-dimensional
representations over a field. The rank of `σ ⟶ X` is invariant under isomorphisms of `X` and
additive on biproducts, so it descends to the additive map
`TauCeti.SplitK0.homFinrank k σ : SplitK0 C →+ ℤ` sending `[X]` to `finrank k (σ ⟶ X)`. For
finite-dimensional representations of a compact group over `ℂ` and an irreducible `σ`, this is
the multiplicity of `σ` in a virtual representation.

The map depends on `σ` only through its isomorphism class, is additive in `σ` and vanishes for a
zero object.

## Main definitions

* `TauCeti.SplitK0.homFinrank k σ`: the additive map `SplitK0 C → ℤ` sending `[X]` to the rank of
  `σ ⟶ X`.

## Main results

* `TauCeti.SplitK0.homFinrank_of`: the value on the class of an object.
* `TauCeti.SplitK0.homFinrank_congr`, `TauCeti.SplitK0.homFinrank_biprod` and
  `TauCeti.SplitK0.homFinrank_eq_zero_of_isZero`: the dependence on `σ`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w v u t

namespace SplitK0

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C] (k : Type t) [Semiring k] [StrongRankCondition k] [Linear k C]

/-- The **Hom rank** of an object `σ` on split `K₀`: the additive map `SplitK0 C → ℤ` sending the
class of `X` to the rank of `σ ⟶ X`. For representations of a compact group over `ℂ` and an
irreducible `σ`, this is the multiplicity of `σ` in a virtual representation. -/
noncomputable def homFinrank (σ : C) [∀ X : C, Module.Free k (σ ⟶ X)]
    [∀ X : C, Module.Finite k (σ ⟶ X)] : SplitK0.{w} C →+ ℤ :=
  lift
    { obj X := Module.finrank k (σ ⟶ X)
      map_iso _ _ e := by rw [(Linear.homCongr k (Iso.refl σ) e).finrank_eq]
      map_biprod X Y := by rw [finrank_homTo_biprod k σ X Y, Nat.cast_add] }

/-- The Hom rank of `σ` sends the class of `X` to the rank of `σ ⟶ X`. -/
@[simp]
theorem homFinrank_of (σ : C) [∀ X : C, Module.Free k (σ ⟶ X)]
    [∀ X : C, Module.Finite k (σ ⟶ X)] (X : C) :
    homFinrank.{w} k σ (of X) = Module.finrank k (σ ⟶ X) :=
  lift_of _ X

variable {k}

/-- Isomorphic objects have the same Hom rank. -/
theorem homFinrank_congr {σ σ' : C} [∀ X : C, Module.Free k (σ ⟶ X)]
    [∀ X : C, Module.Finite k (σ ⟶ X)] [∀ X : C, Module.Free k (σ' ⟶ X)]
    [∀ X : C, Module.Finite k (σ' ⟶ X)] (e : σ ≅ σ') :
    homFinrank.{w} k σ = homFinrank k σ' :=
  hom_ext fun X ↦ by
    rw [homFinrank_of, homFinrank_of, (Linear.homCongr k e (Iso.refl X)).finrank_eq]

variable (k) in
/-- The Hom rank of a biproduct is the sum of the Hom ranks of the summands. -/
@[simp]
theorem homFinrank_biprod (σ τ : C) [∀ X : C, Module.Free k (σ ⟶ X)]
    [∀ X : C, Module.Finite k (σ ⟶ X)] [∀ X : C, Module.Free k (τ ⟶ X)]
    [∀ X : C, Module.Finite k (τ ⟶ X)] :
    homFinrank.{w} k (σ ⊞ τ) = homFinrank k σ + homFinrank k τ :=
  hom_ext fun X ↦ by
    rw [AddMonoidHom.add_apply, homFinrank_of, homFinrank_of, homFinrank_of,
      finrank_hom_biprod k X σ τ, Nat.cast_add]

/-- The Hom rank of a zero object vanishes. -/
theorem homFinrank_eq_zero_of_isZero {σ : C} [∀ X : C, Module.Free k (σ ⟶ X)]
    [∀ X : C, Module.Finite k (σ ⟶ X)] (hσ : IsZero σ) : homFinrank.{w} k σ = 0 :=
  hom_ext fun X ↦ by
    have : Subsingleton (σ ⟶ X) := ⟨hσ.eq_of_src⟩
    rw [homFinrank_of, Module.finrank_zero_of_subsingleton, Nat.cast_zero,
      AddMonoidHom.zero_apply]

end SplitK0

end TauCeti
