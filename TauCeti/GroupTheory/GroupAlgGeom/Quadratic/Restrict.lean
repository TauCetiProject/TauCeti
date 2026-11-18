/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Regular

/-!
# A standard quadratic equation in its own variables

A standard quadratic equation `S : Standard G X` uses the variables `S.vars ⊆ X`, and the other
variables of `X` are absent from it; for instance, bringing a strictly quadratic word into
standard form by an automorphism of `G[X]` can make variables disappear. The equation
`S.restrict : Standard G S.vars` is the same equation with the variables it uses as its variable
type, so that every variable occurs in it (`Standard.vars_restrict`). Renaming the variables of
`S.restrict` along the inclusion `S.vars → X` gives back `S`, and the type, genus, coefficients
and the invariants `r(S)`, `χ(S)` and `κ(S)` are unchanged.

The absent variables are unconstrained coordinates: a point `v : X → H` solves `S` exactly when
its restriction to `S.vars` solves `S.restrict`, so the solutions of `S.restrict` are the
restrictions of the solutions of `S`. Degenerate, commutative and general-position points,
regularity and the radical correspond accordingly. Since every variable of `S.restrict` occurs,
its invariant `κ` is the number of its variables, plus one when the coefficient `d` occurs, which
is how [IFT], Definition 6, counts `κ(S)`
(`TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_card_of_vars_eq_univ`,
`TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_card_add_one_of_vars_eq_univ`); for `S` itself
on a larger set of variables this count fails.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.Standard.restrict`: `S` as an equation in the variables
  `S.vars`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.vars_restrict`: every variable of `S.restrict` occurs
  in it.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.map_toWord_restrict`: renaming the variables of
  `S.restrict` along the inclusion `S.vars → X` gives `S`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.eval_toWord_restrict`: at the restriction of a point
  to `S.vars`, `S.restrict` takes the value of `S`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.comp_val_mem_V_restrict_iff`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.V_restrict`: a point solves `S` exactly when its
  restriction to `S.vars` solves `S.restrict`, and the solutions of `S.restrict` are the
  restrictions of the solutions of `S`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_restrict_iff`: `S.restrict` is regular
  exactly when `S` is; likewise for degenerate, commutative and general-position points.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_restrict`: the radical of `S.restrict` is the
  preimage of the radical of `S` under the inclusion of the variables.
* `TauCeti.GroupAlgGeom.Quadratic.kappa_restrict_conjugate`: over `F(a, b)`, the equation
  `z⁻¹ a z a⁻¹ = 1` in two variables, one of them absent: the count of `κ` by variables holds for
  its restriction and fails for the equation itself.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 2–6.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

variable {G H X : Type*} [Group G] [Group H]

/-- A standard quadratic equation as an equation in the variables it uses: the same type, genus,
coefficients and constant, with the variables `S.vars` as variable type. -/
def restrict : (S : Standard G X) → Standard G S.vars
  | orientable n hn x y inj =>
    orientable n hn (fun i ↦ ⟨x i, by simp⟩) (fun i ↦ ⟨y i, by simp⟩)
      (.of_comp (f := Subtype.val) <| by rwa [Sum.comp_elim])
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    orientableCoeff n m hnm (fun i ↦ ⟨x i, by simp⟩) (fun i ↦ ⟨y i, by simp⟩)
      (fun j ↦ ⟨z j, by simp⟩)
      (.of_comp (f := Subtype.val) <| by rwa [Sum.comp_elim, Sum.comp_elim]) c hc d hd
  | nonorientable n hn x inj =>
    nonorientable n hn (fun i ↦ ⟨x i, by simp⟩) (.of_comp (f := Subtype.val) inj)
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    nonorientableCoeff n m hn (fun i ↦ ⟨x i, by simp⟩) (fun j ↦ ⟨z j, by simp⟩)
      (.of_comp (f := Subtype.val) <| by rwa [Sum.comp_elim]) c hc d hd

variable (S : Standard G X)

/-! ### The equation and its invariants -/

/-- Every variable of `S.restrict` occurs in it. -/
@[simp]
theorem vars_restrict : S.restrict.vars = Set.univ := by
  cases S <;> simp [restrict, Set.eq_univ_iff_forall]

/-- Renaming the atoms of `S.restrict` along the inclusion `S.vars → X` gives the atoms of `S`. -/
@[simp]
theorem map_atoms_restrict :
    S.restrict.atoms.map (Monoid.Coprod.map (MonoidHom.id G) (FreeGroup.map Subtype.val)) =
      S.atoms := by
  cases S <;> simp [restrict, map_commutatorElement, Function.comp_def]

/-- `S.restrict` has the constant coefficient of `S`. -/
@[simp]
theorem constant_restrict : S.restrict.constant = S.constant := by
  cases S <;> simp [restrict]

/-- Renaming the variables of `S.restrict` along the inclusion `S.vars → X` gives `S`. -/
@[simp]
theorem map_toWord_restrict :
    Monoid.Coprod.map (MonoidHom.id G) (FreeGroup.map Subtype.val) S.restrict.toWord =
      S.toWord := by
  simp [toWord_def, map_list_prod]

/-- `S.restrict` has the coefficients of `S`. -/
@[simp]
theorem coeffs_restrict : S.restrict.coeffs = S.coeffs := by
  cases S <;> simp [restrict]

/-- `S.restrict` has the genus of `S`. -/
@[simp]
theorem genus_restrict : S.restrict.genus = S.genus := by
  cases S <;> simp [restrict]

/-- `S.restrict` has the atomic rank of `S`. -/
@[simp]
theorem atomicRank_restrict : S.restrict.atomicRank = S.atomicRank := by
  cases S <;> simp [restrict]

/-- `S.restrict` has the invariant `κ` of `S`. -/
@[simp]
theorem kappa_restrict : S.restrict.kappa = S.kappa := by
  cases S <;> simp [restrict]

/-- `S.restrict` has the Euler characteristic of `S`. -/
@[simp]
theorem eulerChar_restrict : S.restrict.eulerChar = S.eulerChar := by
  cases S <;> simp [restrict]

/-- `S.restrict` is orientable exactly when `S` is. -/
@[simp]
theorem isOrientable_restrict_iff : S.restrict.IsOrientable ↔ S.IsOrientable := by
  cases S <;> simp [restrict]

/-! ### Solutions -/

variable (ι : G →* H)

/-- At the restriction of a point to `S.vars`, the atoms of `S.restrict` take the values of the
atoms of `S`. -/
@[simp]
theorem map_eval_atoms_restrict (v : X → H) :
    S.restrict.atoms.map (eval ι (v ∘ Subtype.val)) = S.atoms.map (eval ι v) := by
  cases S <;> simp [restrict, Function.comp_def, map_commutatorElement]

/-- At the restriction of a point to `S.vars`, `S.restrict` takes the value of `S`. -/
@[simp]
theorem eval_toWord_restrict (v : X → H) :
    eval ι (v ∘ Subtype.val) S.restrict.toWord = eval ι v S.toWord := by
  rw [← map_toWord_restrict S, eval_map, MonoidHom.comp_id]

/-- The restriction of a point to `S.vars` solves `S.restrict` exactly when the point solves
`S`: the variables absent from `S` are unconstrained. -/
theorem comp_val_mem_V_restrict_iff (v : X → H) :
    v ∘ Subtype.val ∈ V ι {S.restrict.toWord} ↔ v ∈ V ι {S.toWord} := by
  simp

/-- The solutions of `S.restrict` are the restrictions to `S.vars` of the solutions of `S`. -/
theorem V_restrict :
    V ι {S.restrict.toWord} = (fun v : X → H ↦ v ∘ Subtype.val) '' V ι {S.toWord} := by
  ext w
  refine ⟨fun hw ↦ ⟨Function.extend Subtype.val w 1, ?_, ?_⟩, ?_⟩
  · rwa [← comp_val_mem_V_restrict_iff, Function.extend_comp Subtype.val_injective]
  · exact Function.extend_comp Subtype.val_injective w 1
  · rintro ⟨v, hv, rfl⟩
    exact (comp_val_mem_V_restrict_iff S ι v).2 hv

/-- The restriction of a point to `S.vars` is degenerate for `S.restrict` exactly when the point
is degenerate for `S`. -/
@[simp]
theorem isDegenerate_restrict_iff (v : X → H) :
    S.restrict.IsDegenerate ι (v ∘ Subtype.val) ↔ S.IsDegenerate ι v := by
  simp only [isDegenerate_iff, ← List.mem_map (f := eval ι _), map_eval_atoms_restrict]

/-- The restriction of a point to `S.vars` is commutative for `S.restrict` exactly when the point
is commutative for `S`. -/
@[simp]
theorem isCommutative_restrict_iff (v : X → H) :
    S.restrict.IsCommutative ι (v ∘ Subtype.val) ↔ S.IsCommutative ι v := by
  rw [isCommutative_iff, isCommutative_iff, map_eval_atoms_restrict]

/-- The restriction of a point to `S.vars` is in general position for `S.restrict` exactly when
the point is in general position for `S`. -/
@[simp]
theorem isGeneralPosition_restrict_iff (v : X → H) :
    S.restrict.IsGeneralPosition ι (v ∘ Subtype.val) ↔ S.IsGeneralPosition ι v := by
  rw [isGeneralPosition_iff, isGeneralPosition_iff, map_eval_atoms_restrict]

/-- `S.restrict` is regular exactly when `S` is. -/
@[simp]
theorem isRegular_restrict_iff : S.restrict.IsRegular ι ↔ S.IsRegular ι := by
  simp [isRegular_def, V_restrict]

/-- The radical of `S.restrict` is the preimage of the radical of `S` under the inclusion of the
variables. -/
theorem Rad_restrict : Rad ι {S.restrict.toWord} = (Rad ι {S.toWord}).comap
    (Monoid.Coprod.map (MonoidHom.id G) (FreeGroup.map Subtype.val)) := by
  ext w
  simp [mem_Rad, V_restrict]

end TauCeti.GroupAlgGeom.Quadratic.Standard

namespace TauCeti.GroupAlgGeom.Quadratic

/-! ### An equation with an absent variable -/

section Examples

/-- Over `F(a, b)`, consider `z⁻¹ a z a⁻¹ = 1` as an equation in the variables `Fin 2`, with
`z = 0`: its only variable is `0`, the variable `1` does not occur. The count `κ(S) = |X| + 1` of
[IFT], Definition 6, holds for its restriction, an equation in the variables `S.vars`, and fails for
the equation in the variables `Fin 2`. -/
theorem kappa_restrict_conjugate :
    let S : Standard (FreeGroup (Fin 2)) (Fin 2) :=
      .orientableCoeff 0 1 one_pos Fin.elim0 Fin.elim0 ![0] (by decide) ![.of 0] (by decide)
        (.of 0)⁻¹ (by decide)
    S.vars = {0} ∧ S.restrict.kappa = Nat.card S.vars + 1 ∧ S.kappa ≠ Nat.card (Fin 2) + 1 := by
  intro S
  refine ⟨by simp [S], S.restrict.kappa_eq_card_add_one_of_vars_eq_univ S.vars_restrict ?_,
    by simp [S]⟩
  simp [S]

end Examples

end TauCeti.GroupAlgGeom.Quadratic
