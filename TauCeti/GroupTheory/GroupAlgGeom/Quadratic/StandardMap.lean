/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Regular
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Standard quadratic equations under a change of the coefficient group

A homomorphism `f : G →* H` that keeps the coefficients of a standard quadratic equation `S` over
`G` nontrivial carries `S` to a standard quadratic equation `S.map f h` over `H` of the same type,
in the same variables, with coefficients `f cⱼ` and `f d`. Solving `S.map f h` in a group receiving
`H` through `ι` is the same as solving `S` through `ι ∘ f`, and the notions attached to solutions
(degenerate, commutative and general-position solutions, regularity) agree.

In a triangular system ([IFT], Definition 43) the equation of a level has coefficients in `G` and
the variables of the lower levels, and is solved over the coordinate group of the lower levels.
Its image under the quotient map is the same equation as a standard quadratic equation over that
group, so results about equations over their own coefficient group apply to it. The coefficients
must stay nontrivial: if `f d = 1`, the image of `[x, y] d = 1` would be `[x, y] = 1`, an equation
of another type.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.Standard.map`: the image of a standard quadratic equation under
  a homomorphism of the coefficient group that keeps its coefficients nontrivial.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.V_toWord_map`: the solutions of `S.map f h` through `ι`
  are the solutions of `S` through `ι ∘ f`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isRegular_map_iff`: `S.map f h` is regular through `ι`
  exactly when `S` is regular through `ι ∘ f`; likewise for degenerate, commutative and
  general-position solutions.
* `TauCeti.GroupAlgGeom.Quadratic.isRegular_commutator_eq_commutator_eval`: over `F(a, b)[t]`, the
  equation `[x, y] = [a, t]` is regular along the specialisation `t ↦ b`.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 3 and 6, and §7.6, Definition 43.
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

variable {G H K X : Type*} [Group G] [Group H] [Group K]

/-- The image of a standard quadratic equation over `G` under a homomorphism `f : G →* H` that
keeps its coefficients nontrivial: the standard quadratic equation over `H` of the same type and
in the same variables, with coefficients `f cⱼ` and `f d`. -/
def map (f : G →* H) : (S : Standard G X) → (∀ g ∈ S.coeffs, f g ≠ 1) → Standard H X
  | orientable n hn x y inj, _ => orientable n hn x y inj
  | orientableCoeff n m hnm x y z inj c _ d _, h =>
    orientableCoeff n m hnm x y z inj (fun j ↦ f (c j)) (fun j ↦ h _ (by simp)) (f d)
      (h _ (by simp))
  | nonorientable n hn x inj, _ => nonorientable n hn x inj
  | nonorientableCoeff n m hn x z inj c _ d _, h =>
    nonorientableCoeff n m hn x z inj (fun j ↦ f (c j)) (fun j ↦ h _ (by simp)) (f d)
      (h _ (by simp))

section Constructors

variable (f : G →* H) {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

/-- An orientable equation without coefficients is its own image. -/
@[simp]
theorem map_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective)
    (h : ∀ g ∈ (orientable n hn x y inj).coeffs, f g ≠ 1) :
    (orientable n hn x y inj).map f h = orientable n hn x y inj := (rfl)

/-- The image of an orientable equation with coefficients `cⱼ` and `d` is the same equation with
coefficients `f cⱼ` and `f d`. -/
@[simp]
theorem map_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1)
    (h : ∀ g ∈ (orientableCoeff n m hnm x y z inj c hc d hd).coeffs, f g ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).map f h =
      orientableCoeff n m hnm x y z inj (fun j ↦ f (c j)) (fun j ↦ h _ (by simp)) (f d)
        (h _ (by simp)) := (rfl)

/-- A non-orientable equation without coefficients is its own image. -/
@[simp]
theorem map_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective)
    (h : ∀ g ∈ (nonorientable n hn x inj).coeffs, f g ≠ 1) :
    (nonorientable n hn x inj).map f h = nonorientable n hn x inj := (rfl)

/-- The image of a non-orientable equation with coefficients `cⱼ` and `d` is the same equation
with coefficients `f cⱼ` and `f d`. -/
@[simp]
theorem map_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1)
    (h : ∀ g ∈ (nonorientableCoeff n m hn x z inj c hc d hd).coeffs, f g ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).map f h =
      nonorientableCoeff n m hn x z inj (fun j ↦ f (c j)) (fun j ↦ h _ (by simp)) (f d)
        (h _ (by simp)) := (rfl)

end Constructors

variable (f : G →* H) (S : Standard G X) (h : ∀ g ∈ S.coeffs, f g ≠ 1)

/-- The atoms of the image equation are the images of the atoms of `S`: each coefficient `g` is
replaced by `f g` and the variables are unchanged. -/
@[simp]
theorem atoms_map :
    (S.map f h).atoms = S.atoms.map (Monoid.Coprod.map f (FreeGroup.map id)) := by
  cases S <;> simp [Function.comp_def]

/-- The constant coefficient of the image equation is the image of the constant coefficient. -/
@[simp]
theorem constant_map : (S.map f h).constant = f S.constant := by
  cases S <;> simp

/-- The left side of the image equation is the left side of `S` with each coefficient `g`
replaced by `f g` and the variables unchanged. -/
@[simp]
theorem toWord_map :
    (S.map f h).toWord = Monoid.Coprod.map f (FreeGroup.map id) S.toWord := by
  simp [toWord_def, map_list_prod]

/-- The coefficients of the image equation are the images of the coefficients of `S`. -/
@[simp]
theorem coeffs_map : (S.map f h).coeffs = S.coeffs.map f := by
  cases S <;> simp [Function.comp_def]

/-- The image equation has the variables of `S`. -/
@[simp]
theorem vars_map : (S.map f h).vars = S.vars := by
  cases S <;> simp

/-- The image equation has the invariant `κ` of `S`. -/
@[simp]
theorem kappa_map : (S.map f h).kappa = S.kappa := by
  cases S <;> simp

/-- The image equation has the genus of `S`. -/
@[simp]
theorem genus_map : (S.map f h).genus = S.genus := by
  cases S <;> simp

/-- The image equation has the atomic rank of `S`. -/
@[simp]
theorem atomicRank_map : (S.map f h).atomicRank = S.atomicRank := by
  simp [atomicRank_def]

/-- The image equation has the Euler characteristic of `S`. -/
@[simp]
theorem eulerChar_map : (S.map f h).eulerChar = S.eulerChar := by
  cases S <;> simp

/-- The image equation is orientable exactly when `S` is. -/
@[simp]
theorem isOrientable_map_iff : (S.map f h).IsOrientable ↔ S.IsOrientable := by
  cases S <;> simp

/-- Changing the coefficients along the identity does not change the equation. -/
@[simp]
theorem map_id (h : ∀ g ∈ S.coeffs, MonoidHom.id G g ≠ 1) : S.map (.id G) h = S := by
  cases S <;> rfl

/-- Changing the coefficients along `f` and then along `g` is changing them along `g ∘ f`. -/
@[simp]
theorem map_map (g : H →* K) (hg : ∀ k ∈ (S.map f h).coeffs, g k ≠ 1) :
    (S.map f h).map g hg =
      S.map (g.comp f) fun k hk ↦ hg (f k) (coeffs_map f S h ▸ List.mem_map_of_mem hk) := by
  cases S <;> rfl

/-- The solutions of the image equation through `ι` are the solutions of `S` through `ι ∘ f`. -/
theorem V_toWord_map (ι : H →* K) : V ι {(S.map f h).toWord} = V (ι.comp f) {S.toWord} := by
  ext v
  simp

/-- A point is degenerate for the image equation through `ι` exactly when it is degenerate for `S`
through `ι ∘ f`: the atoms of the image take the values of the atoms of `S`. -/
@[simp]
theorem isDegenerate_map_iff (ι : H →* K) (v : X → K) :
    (S.map f h).IsDegenerate ι v ↔ S.IsDegenerate (ι.comp f) v := by
  simp [isDegenerate_iff]

/-- A point is commutative for the image equation through `ι` exactly when it is commutative for
`S` through `ι ∘ f`. -/
@[simp]
theorem isCommutative_map_iff (ι : H →* K) (v : X → K) :
    (S.map f h).IsCommutative ι v ↔ S.IsCommutative (ι.comp f) v := by
  simp [isCommutative_iff, Function.comp_def]

/-- A point is in general position for the image equation through `ι` exactly when it is in
general position for `S` through `ι ∘ f`. -/
@[simp]
theorem isGeneralPosition_map_iff (ι : H →* K) (v : X → K) :
    (S.map f h).IsGeneralPosition ι v ↔ S.IsGeneralPosition (ι.comp f) v := by
  simp [isGeneralPosition_iff, Function.comp_def]

/-- The image equation is regular through `ι` exactly when `S` is regular through `ι ∘ f`. -/
@[simp]
theorem isRegular_map_iff (ι : H →* K) : (S.map f h).IsRegular ι ↔ S.IsRegular (ι.comp f) := by
  have hd : f S.constant = 1 ↔ S.constant = 1 := by
    cases S <;> simp_all
  rw [isRegular_def, isRegular_def, V_toWord_map]
  simp [hd]

end TauCeti.GroupAlgGeom.Quadratic.Standard

namespace TauCeti.GroupAlgGeom.Quadratic

open scoped commutatorElement

/-! ### A level over a lower group -/

section Examples

/-- Over `F(a, b)[t]`, the equation `[x, y] = [a, t]` is regular along the specialisation
`t ↦ b`: its image over `F(a, b)` is the regular equation `[x, y] = [a, b]`. -/
theorem isRegular_commutator_eq_commutator_eval :
    (Standard.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0 (by simp)
      ⁅(inl (FreeGroup.of 0) : GX (FreeGroup (Fin 2)) Unit)⁻¹,
        (inr (FreeGroup.of ()) : GX (FreeGroup (Fin 2)) Unit)⁻¹⁆⁻¹
      (by simpa [commutatorElement_eq_one_iff_commute, Commute.symm_iff] using
        GX.not_commute_inl_inr_of (FreeGroup.of_ne_one (0 : Fin 2)) ()) :
        Standard (GX (FreeGroup (Fin 2)) Unit) (Fin 2)).IsRegular
      (eval (.id _) fun _ ↦ FreeGroup.of 1) := by
  -- regularity along a coefficient map is regularity of the image equation over its target
  have key (S : Standard (GX (FreeGroup (Fin 2)) Unit) (Fin 2))
      (f : GX (FreeGroup (Fin 2)) Unit →* FreeGroup (Fin 2)) (h : ∀ g ∈ S.coeffs, f g ≠ 1)
      (hS : (S.map f h).IsRegular (.id _)) : S.IsRegular f := by
    simpa using (Standard.isRegular_map_iff f S h (.id _)).1 hS
  refine key _ _ (by simp +decide) ?_
  -- the image is the equation `[x, y] = [a, b]` over `F(a, b)`
  convert isRegular_commutator_eq_commutator using 1
  simp [commutatorElement_def, funext_iff]

end Examples

end TauCeti.GroupAlgGeom.Quadratic
