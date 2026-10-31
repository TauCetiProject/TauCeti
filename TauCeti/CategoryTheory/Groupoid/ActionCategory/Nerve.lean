/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import TauCeti.Order.Fin.Induction

/-!
# Strings of composable arrows of an action category

For a monoid `G` acting on `X`, a string of `n` composable arrows `x₀ ⟶ x₁ ⟶ ⋯ ⟶ xₙ` of the
action category `CategoryTheory.ActionCategory G X` is determined by its first point `x₀` and the
labels `gₖ` of its consecutive arrows, with `xₖ₊₁ = gₖ • xₖ`. This file proves the facts about
labels along a string behind this description, and the resulting bijection
`TauCeti.ActionGroupoid.nerveEquiv` between the `n`-simplices of the nerve and `X × Gⁿ`. Every
label is retained, including labels acting trivially.

For a group action, all points of a string lie in one orbit
(`TauCeti.ActionGroupoid.quotient_mk_back_obj`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  Section 3.
-/

public noncomputable section

open CategoryTheory CategoryTheory.ActionCategory

namespace TauCeti.ActionGroupoid

section Monoid

variable {G X : Type*} [Monoid G] [MulAction G X] {n : ℕ}

/-- In a string of composable arrows of an action category, the arrow from the `i`-th object to
itself has label `1`. -/
theorem hom_map_homOfLE_refl (F : ComposableArrows (ActionCategory G X) n)
    (i : Fin (n + 1)) : (F.map (homOfLE (le_refl i))).hom = (1 : G) := by
  simp

/-- In a string of composable arrows of an action category, the label of the arrow from the `i`-th
to the `(k + 1)`-th object is the `k`-th consecutive label times the label of the arrow from the
`i`-th to the `k`-th object. -/
theorem hom_map_homOfLE_succ (F : ComposableArrows (ActionCategory G X) n)
    {i : Fin (n + 1)} {k : Fin n} (hik : i ≤ k.castSucc) :
    (F.map (homOfLE (hik.trans k.castSucc_le_succ))).hom =
      ((F.map (homOfLE k.castSucc_le_succ)).hom : G) * (F.map (homOfLE hik)).hom := by
  rw [← homOfLE_comp, F.map_comp, ActionCategory.comp_hom]

/-- The point underlying the `i`-th object of a string of composable arrows of an action category
is the label of the arrow from the first object, applied to the first point. -/
theorem back_obj_eq_smul (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (F.obj i).back = ((F.map (homOfLE (Fin.zero_le i))).hom : G) • (F.obj 0).back :=
  (F.map (homOfLE (Fin.zero_le i))).map_val.symm

/-- Two strings of composable arrows of an action category with the same first point and the
same consecutive labels are equal. -/
theorem nerve_ext {F F' : ComposableArrows (ActionCategory G X) n}
    (h₀ : (F.obj 0).back = (F'.obj 0).back)
    (h : ∀ k : Fin n, (F.map (homOfLE k.castSucc_le_succ)).hom =
      ((F'.map (homOfLE k.castSucc_le_succ)).hom : G)) : F = F' := by
  have hlabel : ∀ i j (hij : i ≤ j),
      (F.map (homOfLE hij)).hom = ((F'.map (homOfLE hij)).hom : G) :=
    Fin.le_induction_castSucc (fun i ↦ by rw [hom_map_homOfLE_refl F, hom_map_homOfLE_refl F'])
      fun i k hik ih ↦ by rw [hom_map_homOfLE_succ F hik, hom_map_homOfLE_succ F' hik, ih, h]
  have hobj (i : Fin (n + 1)) : F.obj i = F'.obj i := by
    rw [← back_coe (F.obj i), ← back_coe (F'.obj i), back_obj_eq_smul F i, back_obj_eq_smul F' i,
      h₀, hlabel]
  refine ComposableArrows.ext hobj fun i hi ↦ Functor.Elements.Hom.ext ?_
  simp only [ComposableArrows.map', ActionCategory.comp_hom, eqToHom_hom, one_mul, mul_one]
  exact hlabel _ _ _

/-- The consecutive labels of a string built by `ComposableArrows.mkOfObjOfMapSucc` are the labels
of the given arrows. -/
theorem hom_map_mkOfObjOfMapSucc (obj : Fin (n + 1) → ActionCategory G X)
    (mapSucc : ∀ k : Fin n, obj k.castSucc ⟶ obj k.succ) (k : Fin n) :
    ((ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map (homOfLE k.castSucc_le_succ)).hom =
      ((mapSucc k).hom : G) :=
  congrArg (fun f ↦ Functor.Elements.Hom.hom f)
    (ComposableArrows.mkOfObjOfMapSucc_map_succ obj mapSucc k.1 k.2)

variable (G X n) in
/-- The `n`-simplices of the nerve of an action category correspond to `X × Gⁿ`, by recording the
first point and the labels of the consecutive arrows of a string. The string with first point `x`
and labels `g` has `k`-th point `gₖ₋₁ ⋯ g₀ • x`. -/
def nerveEquiv : ComposableArrows (ActionCategory G X) n ≃ X × (Fin n → G) where
  toFun F := ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom)
  invFun p := ComposableArrows.mkOfObjOfMapSucc
    (fun i ↦ ((Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) i).unop • p.1 : X))
    -- The side condition of `homMk` in an action category is `g • x = y` by definition, as in
    -- `ActionCategory.nonempty_hom_iff`.
    fun k ↦ Functor.Elements.homMk (p.2 k)
      (show p.2 k • ((Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) k.castSucc).unop • p.1) =
          (Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) k.succ).unop • p.1 by
        rw [Fin.partialProd_succ, MulOpposite.unop_mul, MulOpposite.unop_op, mul_smul])
  left_inv F := nerve_ext (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) fun k ↦ by
    rw [hom_map_mkOfObjOfMapSucc]
  right_inv p := Prod.ext (by simp [ComposableArrows.mkOfObjOfMapSucc_obj]) <| funext fun k ↦ by
    dsimp only
    rw [hom_map_mkOfObjOfMapSucc]

@[simp]
theorem nerveEquiv_apply (F : ComposableArrows (ActionCategory G X) n) :
    nerveEquiv G X n F = ((F.obj 0).back, fun k ↦ (F.map (homOfLE k.castSucc_le_succ)).hom) :=
  (rfl)

/-- The `i`-th point of the string with first point `x` and consecutive labels `g` is
`gᵢ₋₁ ⋯ g₀ • x`. -/
@[simp]
theorem back_obj_nerveEquiv_symm (p : X × (Fin n → G)) (i : Fin (n + 1)) :
    (((nerveEquiv G X n).symm p).obj i).back =
      (Fin.partialProd (fun k ↦ MulOpposite.op (p.2 k)) i).unop • p.1 := (rfl)

/-- The `k`-th consecutive label of the string with first point `x` and consecutive labels `g` is
`gₖ`. -/
@[simp]
theorem label_nerveEquiv_symm (p : X × (Fin n → G)) (k : Fin n) :
    ((((nerveEquiv G X n).symm p).map (homOfLE k.castSucc_le_succ)).hom : G) = p.2 k :=
  congrFun (congrArg Prod.snd ((nerveEquiv G X n).apply_symm_apply p)) k

end Monoid

section Group

variable {G X : Type*} [Group G] [MulAction G X] {n : ℕ}

/-- All points of a string of composable arrows of an action groupoid lie in one orbit. -/
theorem quotient_mk_back_obj (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (⟦(F.obj i).back⟧ : MulAction.orbitRel.Quotient G X) = ⟦(F.obj 0).back⟧ := by
  rw [back_obj_eq_smul F i, MulAction.orbitRel.Quotient.quotient_smul_eq]

end Group

end TauCeti.ActionGroupoid
