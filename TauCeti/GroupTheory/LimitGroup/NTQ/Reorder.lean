/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.FreeVariables
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardMap
public import TauCeti.GroupTheory.LimitGroup.NTQ.Regular

/-!
# Reordering the levels of a regular NTQ system

An empty level of a triangular quasi-quadratic system adds free variables and no equations. Its
variables can therefore be moved below a quadratic level without changing the set of equations, up
to renaming the variables, and two adjacent empty levels can be merged. A closed genus-two level
`[x₁, y₁][x₂, y₂] = 1` can be split into an empty level in `x₂, y₂` below the level
`[x₁, y₁] [x₂, y₂] = 1` in `x₁, y₁`, whose coefficient `[x₂, y₂]` is a word in the lower variables:
again the equations are the same up to renaming ([IFT], §7.2, the trick for the equation
`[x₁, y₁][x₂, y₂] = 1`, which views it as `[x₁, y₁] = [y₂, x₂]` over the group of constants
`G ∗ F(x₂, y₂)`).

These moves keep a regular system regular, the split as long as the base group `G` is not
commutative. The coordinate group of a system embeds in that of the system extended by free
variables, so a regular quadratic level stays regular when an empty level is moved below it; the
split of a closed genus-two level is regular exactly when the lower system is regular and `G` is
not commutative.

## Main definitions

* `TauCeti.LimitGroup.NTQ.System.swapEmpty`: the system `cons (cons U₃ X₁ empty) X₂ (quadratic Q')`
  obtained from `cons (cons U₃ X₂ (quadratic Q)) X₁ empty` by moving the empty level down.
* `TauCeti.LimitGroup.NTQ.System.splitGenusTwo`: the system with an empty level in two variables
  over `U₂` and the level `[x₁, y₁] [x₂, y₂] = 1` above it.

## Main results

* `TauCeti.LimitGroup.NTQ.System.image_equations_swapEmpty`,
  `TauCeti.LimitGroup.NTQ.System.IsRegular.swapEmpty`: the swapped system has the same equations
  up to renaming the variables, and it is regular when the original system is.
* `TauCeti.LimitGroup.NTQ.System.image_equations_cons_sum_empty`: one empty level in `X₁ ⊕ X₂`
  has the equations of two adjacent empty levels in `X₁` and `X₂`, after reassociating the
  variables.
* `TauCeti.LimitGroup.NTQ.System.image_equations_splitGenusTwo`,
  `TauCeti.LimitGroup.NTQ.System.isRegular_splitGenusTwo_iff`: the split of a closed genus-two top
  level has the same equations up to renaming the variables, and it is regular exactly when the
  lower system is regular and the base group is not commutative.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.6, Definition 43 and Theorem 11; §7.2, p. 99.
-/

public section

namespace TauCeti.LimitGroup.NTQ.System

open GroupAlgGeom Monoid.Coprod
open scoped commutatorElement

universe u v

variable {G : Type u} [Group G]

/-! ### Moving an empty level below a quadratic level -/

section Swap

variable {Y₃ X₂ : Type v} [Finite X₂]

/-- Moving the empty top level `X₁` of `cons (cons U₃ X₂ (quadratic Q)) X₁ empty` below the
quadratic level: the system `cons (cons U₃ X₁ empty) X₂ (quadratic Q')`, where `Q'` is `Q` with its
coefficients `G[Y₃]` read in `G[X₁ ⊕ Y₃]`. -/
noncomputable def swapEmpty (U₃ : System G Y₃) (X₁ : Type v) [Finite X₁]
    (Q : Quadratic.Standard (GX G Y₃) X₂) : System G (X₂ ⊕ (X₁ ⊕ Y₃)) :=
  cons (cons U₃ X₁ .empty) X₂
    (.quadratic (Q.map (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr)) fun _ hg =>
      (map_ne_one_iff _ map_inr_injective).2 (Quadratic.Standard.ne_one_of_mem_coeffs hg)))

theorem swapEmpty_def (U₃ : System G Y₃) (X₁ : Type v) [Finite X₁]
    (Q : Quadratic.Standard (GX G Y₃) X₂) :
    swapEmpty U₃ X₁ Q = cons (cons U₃ X₁ .empty) X₂
      (.quadratic (Q.map (Monoid.Coprod.map (.id G) (FreeGroup.map Sum.inr)) fun _ hg =>
        (map_ne_one_iff _ map_inr_injective).2 (Quadratic.Standard.ne_one_of_mem_coeffs hg))) :=
  (rfl)

/-- The swapped system has the equations of `cons (cons U₃ X₂ (quadratic Q)) X₁ empty`, after
renaming its variables `X₂ ⊕ (X₁ ⊕ Y₃)` as `X₁ ⊕ (X₂ ⊕ Y₃)`. -/
theorem image_equations_swapEmpty (U₃ : System G Y₃) (X₁ : Type v) [Finite X₁]
    (Q : Quadratic.Standard (GX G Y₃) X₂) :
    Monoid.Coprod.map (.id G) (FreeGroup.map
        (Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)))) ''
        (swapEmpty U₃ X₁ Q).equations =
      (cons (cons U₃ X₂ (.quadratic Q)) X₁ .empty).equations := by
  simp only [swapEmpty_def, equations_cons, Level.equations_empty, Level.equations_quadratic,
    Set.image_empty, Set.union_empty, Set.image_union, Set.image_image, Set.image_singleton,
    GX.map_map, MonoidHom.comp_id, Quadratic.Standard.toWord_map]
  congr 2
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply]
  congr 1
  ext <;> simp

/-- Moving an empty top level below a quadratic level keeps a system regular. -/
theorem IsRegular.swapEmpty {U₃ : System G Y₃} {X₁ : Type v} [Finite X₁]
    {Q : Quadratic.Standard (GX G Y₃) X₂}
    (h : (cons (cons U₃ X₂ (.quadratic Q)) X₁ .empty).IsRegular) :
    (swapEmpty U₃ X₁ Q).IsRegular := by
  obtain ⟨hU, hX, hQ⟩ := isRegular_cons_quadratic.1 (isRegular_cons_empty.1 h)
  have hR := comap_Rad_cons_empty (ι := .id G) U₃ X₁
  rw [swapEmpty_def]
  refine isRegular_cons_quadratic.2 ⟨isRegular_cons_empty.2 hU,
    by simp [Quadratic.Standard.vars_map, hX], ?_⟩
  exact (Quadratic.Standard.isRegular_map_iff _ _ _ _).2 <|
    hQ.map ⟨QuotientGroup.map _ _ _ hR.ge, fun _ => rfl⟩
      ((QuotientGroup.map_injective_iff _ _ _ hR.ge).2 hR.le)

end Swap

/-! ### Merging two empty levels -/

/-- Two adjacent empty levels in `X₁` over `X₂` have the equations of one empty level in
`X₁ ⊕ X₂`, after reassociating the variables. -/
theorem image_equations_cons_sum_empty {Y₃ X₂ X₁ : Type v} [Finite X₂] [Finite X₁]
    (U₃ : System G Y₃) :
    Monoid.Coprod.map (.id G) (FreeGroup.map (Equiv.sumAssoc X₁ X₂ Y₃)) ''
        (cons U₃ (X₁ ⊕ X₂) .empty).equations =
      (cons (cons U₃ X₂ .empty) X₁ .empty).equations := by
  simp [equations_cons, Set.image_image, GX.map_map, Function.comp_def]

/-! ### Splitting a closed genus-two level -/

section Split

variable {Y₂ : Type v}

/-- The split of a closed genus-two level over `U₂`: an empty level in variables `x₂, y₂` over
`U₂`, and above it the level `[x₁, y₁] [x₂, y₂] = 1` in variables `x₁, y₁`, a standard equation of
genus one whose constant `[x₂, y₂]` is a word in the lower variables. Here, as in [IFT],
`[a, b] = a⁻¹ b⁻¹ a b`, which is `⁅a⁻¹, b⁻¹⁆` in Lean. -/
noncomputable def splitGenusTwo (U₂ : System G Y₂) :
    System G (ULift.{v} (Fin 2) ⊕ (ULift.{v} (Fin 2) ⊕ Y₂)) :=
  cons (cons U₂ (ULift.{v} (Fin 2)) .empty) (ULift.{v} (Fin 2))
    (.quadratic (.orientableCoeff 1 0 one_pos ![⟨0⟩] ![⟨1⟩] Fin.elim0 (by decide) Fin.elim0
      (fun j => j.elim0) ⁅(inr (FreeGroup.of (.inl ⟨0⟩)) : GX G (ULift.{v} (Fin 2) ⊕ Y₂))⁻¹,
        (inr (FreeGroup.of (.inl ⟨1⟩)))⁻¹⁆
      fun h => GX.not_commute_inr_of_inr_of (by simp)
        (Commute.inv_inv_iff.1 (commutatorElement_eq_one_iff_commute.1 h))))

theorem splitGenusTwo_def (U₂ : System G Y₂) :
    splitGenusTwo U₂ = cons (cons U₂ (ULift.{v} (Fin 2)) .empty) (ULift.{v} (Fin 2))
      (.quadratic (.orientableCoeff 1 0 one_pos ![⟨0⟩] ![⟨1⟩] Fin.elim0 (by decide) Fin.elim0
        (fun j => j.elim0) ⁅(inr (FreeGroup.of (.inl ⟨0⟩)) : GX G (ULift.{v} (Fin 2) ⊕ Y₂))⁻¹,
          (inr (FreeGroup.of (.inl ⟨1⟩)))⁻¹⁆
        fun h => GX.not_commute_inr_of_inr_of (by simp)
          (Commute.inv_inv_iff.1 (commutatorElement_eq_one_iff_commute.1 h)))) :=
  (rfl)

/-- The split of a closed genus-two top level has the equations of
`cons U₂ X₁ (quadratic [x 0, y 0][x 1, y 1])`, after renaming the variables of its top level as
`x 0, y 0` and those of its empty level as `x 1, y 1`. -/
theorem image_equations_splitGenusTwo {X₁ : Type v} [Finite X₁] (U₂ : System G Y₂)
    {x y : Fin 2 → X₁} (inj : (Sum.elim x y).Injective) :
    Monoid.Coprod.map (.id G) (FreeGroup.map
        (Sum.elim (fun i => Sum.inl (![x 0, y 0] i.down))
          (Sum.elim (fun i => Sum.inl (![x 1, y 1] i.down)) Sum.inr))) ''
        (splitGenusTwo U₂).equations =
      (cons U₂ X₁ (.quadratic (.orientable 2 two_pos x y inj))).equations := by
  simp only [splitGenusTwo_def, equations_cons, Level.equations_empty, Level.equations_quadratic,
    Set.image_empty, Set.union_empty, Set.image_union, Set.image_image, Set.image_singleton,
    GX.map_map, MonoidHom.comp_id]
  congr 2
  simp [Quadratic.Standard.toWord_def, List.ofFn_succ, commutatorElement_def, mul_assoc]

/-- The split of a closed genus-two level over `U₂` is regular exactly when `U₂` is regular and
the base group is not commutative: the coefficient `[x₂, y₂]` stays nontrivial in the coordinate
group of the lower system extended by `x₂, y₂` exactly then, and `x₁ = y₂`, `y₁ = x₂` solves the top
level there. -/
@[simp]
theorem isRegular_splitGenusTwo_iff {U₂ : System G Y₂} :
    (splitGenusTwo U₂).IsRegular ↔ U₂.IsRegular ∧ ∃ g h : G, ¬Commute g h := by
  refine ⟨fun h => ⟨isRegular_cons_empty.1 h.of_cons, ?_⟩, fun ⟨hU, g, h, hgh⟩ => ?_⟩
  · -- Over a commutative group the coefficient `[x₂, y₂]` vanishes at every solution.
    by_contra! hc
    refine ((Quadratic.Standard.isRegular_orientableCoeff_one_zero_iff ..).1
      (isRegular_cons_quadratic.1 h).2.2).1 ?_
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_Rad]
    intro v _
    simp [commutatorElement_eq_one_iff_commute, hc]
  obtain ⟨v₂, hv₂⟩ := hU.isNondegenerate.nonempty_V
  refine isRegular_cons_quadratic.2 ⟨isRegular_cons_empty.2 hU, ?_,
    (Quadratic.Standard.isRegular_orientableCoeff_one_zero_iff ..).2 ⟨?_, ?_⟩⟩
  · simp [Set.eq_univ_iff_forall, ULift.forall, Fin.forall_fin_two,
      Quadratic.Standard.vars_orientableCoeff]
  · -- The point `x₂ = g`, `y₂ = h` over a solution of `U₂` does not kill `[x₂, y₂]`.
    rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_Rad]
    push Not
    refine ⟨Sum.elim (fun i => ![g, h] i.down) v₂, mem_V_cons.2 ⟨by simpa using hv₂, by simp⟩, ?_⟩
    simpa [commutatorElement_eq_one_iff_commute] using hgh
  · refine ⟨fun i => ![QuotientGroup.mk (inr (FreeGroup.of (Sum.inl (⟨1⟩ : ULift.{v} (Fin 2))))
      : GX G (ULift.{v} (Fin 2) ⊕ Y₂)), QuotientGroup.mk (inr (FreeGroup.of (Sum.inl
        (⟨0⟩ : ULift.{v} (Fin 2)))) : GX G (ULift.{v} (Fin 2) ⊕ Y₂))] i.down, ?_⟩
    simp [Quadratic.Standard.toWord_def, commutatorElement_def, mul_assoc]

end Split

/-! ### Examples -/

section Examples

/-- Over `F(a, b)`, splitting the upper of the two disjoint closed genus-two levels
`[u₁, v₁][u₂, v₂] = 1` and `[x₁, y₁][x₂, y₂] = 1` gives a regular system. -/
example : (splitGenusTwo (cons (G := FreeGroup (Fin 2)) nil (Fin 2 ⊕ Fin 2)
    (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
      (by simp [Function.injective_id]))))).IsRegular :=
  isRegular_splitGenusTwo_iff.2 ⟨isRegular_genusTwo_level, FreeGroup.of 0, FreeGroup.of 1, by
    rw [Commute, SemiconjBy]; decide⟩

/-- Over the commutative group `ℤ`, splitting the regular one-level system `[x₁, y₁][x₂, y₂] = 1`
does not give a regular system. -/
example : ¬(splitGenusTwo (G := Multiplicative ℤ) nil).IsRegular := by
  simp [Commute.all]

/-- Over `F(a, b)`, moving an empty level in one variable below the closed genus-two level
`[x₁, y₁][x₂, y₂] = 1` gives a regular system. -/
example : (swapEmpty (G := FreeGroup (Fin 2)) nil (Fin 1)
    (.orientable 2 two_pos Sum.inl Sum.inr (by simp [Function.injective_id]) :
      Quadratic.Standard (GX (FreeGroup (Fin 2)) PEmpty) (Fin 2 ⊕ Fin 2))).IsRegular :=
  IsRegular.swapEmpty (isRegular_cons_empty.2 isRegular_genusTwo_level)

end Examples

end TauCeti.LimitGroup.NTQ.System
