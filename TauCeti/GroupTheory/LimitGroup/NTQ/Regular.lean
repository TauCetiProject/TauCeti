/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Regular
public import TauCeti.GroupTheory.LimitGroup.NTQ.Basic

/-!
# Regular NTQ systems

A raw triangular quasi-quadratic system is *regular* when each of its levels is either empty or a
standard quadratic equation in all the variables of the level which is regular, in the sense of
`TauCeti.GroupAlgGeom.Quadratic.Standard.IsRegular`, over the coordinate group of the lower levels,
its coefficients being read there through the quotient map. Regular quadratic equations have
solutions, so a regular system is nondegenerate: it is an NTQ system. In the examples, commutators
are `[a, b] = a⁻¹ b⁻¹ a b`, as in [IFT]; in Lean this is `⁅a⁻¹, b⁻¹⁆`.

This is the notion of [IFT], Definition 43, under which the implicit function theorem for NTQ
systems is proved there. [KM06], §2, calls an NTQ system regular already when each of its non-empty
quadratic levels is regular, so that levels of types (2) and (3) are allowed as well; that wider
notion is not the one defined here.

## Main definitions

* `TauCeti.LimitGroup.NTQ.System.IsRegular`: regular raw TQ systems.

## Main results

* `TauCeti.LimitGroup.NTQ.System.IsRegular.isNondegenerate`: a regular system is nondegenerate.
* `TauCeti.LimitGroup.NTQ.System.isRegular_cons_genusTwo`: a genus-two level
  `[x₁, y₁][x₂, y₂] = 1` in all its variables keeps a system regular.
* `TauCeti.LimitGroup.NTQ.isRegular_two_genusTwo_levels`: two disjoint genus-two levels form a
  regular system.
* `TauCeti.LimitGroup.NTQ.isRegular_commutator_eq_commutator_over_genusTwo_iff`: the level
  `[x, y] = [u₁, v₁]` over the genus-two level `[u₁, v₁][u₂, v₂] = 1` gives a regular system
  exactly when the base group is not commutative.
* `TauCeti.LimitGroup.NTQ.not_isRegular_relator_coeff_over_genusTwo`: a level whose coefficient is
  the relator `[u₁, v₁][u₂, v₂]` of the lower level is not regular, since the coefficient vanishes
  in the lower coordinate group.
* `TauCeti.LimitGroup.NTQ.isNondegenerate_nonorientable_three_level`,
  `TauCeti.LimitGroup.NTQ.not_isRegular_nonorientable_three_level`: the one-level system
  `x₁² x₂² x₃² = 1` is nondegenerate but not regular.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.6, Definition 43, and §2.7, Definitions 3 and 6.
* [KM06] O. Kharlampovich, A. Myasnikov, *Elementary theory of free non-abelian groups*,
  J. Algebra 302 (2006), §2.
-/

public section

namespace TauCeti.LimitGroup.NTQ

open GroupAlgGeom Monoid.Coprod
open scoped commutatorElement

universe u v

variable {G : Type u} [Group G]

namespace System

/-- A raw TQ system is *regular* when each level is either an empty level (of type (4)) or a
standard quadratic equation in all the variables of the level which is regular over the coordinate
group of the lower levels. Levels of types (2) and (3) are not regular, even without variables. -/
def IsRegular : {Y : Type v} → System G Y → Prop
  | _, nil => True
  | _, cons S _ (.quadratic Q) => S.IsRegular ∧ Q.vars = Set.univ ∧
      Q.IsRegular (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations))
  | _, cons S _ .empty => S.IsRegular
  | _, cons _ _ (.centralizer _ _) => False
  | _, cons _ _ .abelian => False

@[simp]
theorem isRegular_nil : (nil : System G PEmpty).IsRegular := trivial

variable {Y X : Type v} [Finite X] {S : System G Y}

@[simp]
theorem isRegular_cons_quadratic {Q : Quadratic.Standard (GX G Y) X} :
    (cons S X (.quadratic Q)).IsRegular ↔ S.IsRegular ∧ Q.vars = Set.univ ∧
      Q.IsRegular (QuotientGroup.mk' (Rad (MonoidHom.id G) S.equations)) :=
  Iff.rfl

@[simp]
theorem isRegular_cons_empty : (cons S X .empty).IsRegular ↔ S.IsRegular :=
  Iff.rfl

/-- A level of an extension of a centralizer is not regular. -/
@[simp]
theorem not_isRegular_cons_centralizer {U : Set (GX G Y)} {hU : U.Finite} :
    ¬(cons S X (.centralizer U hU)).IsRegular :=
  fun h => h

/-- An abelian level is not regular. -/
@[simp]
theorem not_isRegular_cons_abelian : ¬(cons S X .abelian).IsRegular :=
  fun h => h

/-- The lower system of a regular system is regular. -/
theorem IsRegular.of_cons {L : Level (GX G Y) X} (h : (cons S X L).IsRegular) : S.IsRegular := by
  cases L with
  | quadratic Q => exact h.1
  | empty => exact h
  | centralizer | abelian => exact h.elim

/-- A regular TQ system is nondegenerate. -/
theorem IsRegular.isNondegenerate (h : S.IsRegular) : S.IsNondegenerate := by
  induction S with
  | nil => exact isNondegenerate_nil
  | cons S X L ih =>
    refine isNondegenerate_cons.2 ⟨ih h.of_cons, ?_⟩
    cases L with
    | quadratic Q => simpa using h.2.2.nonempty_V
    | empty => simp
    | centralizer | abelian => exact h.elim

/-- A genus-two level `[x₁, y₁][x₂, y₂] = 1` in all its variables keeps a system regular. -/
theorem isRegular_cons_genusTwo {x y : Fin 2 → X} (inj : (Sum.elim x y).Injective)
    (hxy : Function.Surjective (Sum.elim x y)) :
    (cons S X (.quadratic (.orientable 2 two_pos x y inj))).IsRegular ↔ S.IsRegular :=
  isRegular_cons_quadratic.trans <| and_iff_left
    ⟨(Quadratic.Standard.vars_orientable _ inj).trans (Set.range_eq_univ.2 hxy),
      Quadratic.Standard.isRegular_genusTwo _ inj⟩

end System

/-! ### Examples -/

section Examples

/-- The one-level system `[x₁, y₁][x₂, y₂] = 1` is regular. -/
theorem isRegular_genusTwo_level :
    (System.cons (G := G) .nil (Fin 2 ⊕ Fin 2)
      (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
        (by simp [Function.injective_id])))).IsRegular :=
  (System.isRegular_cons_genusTwo _ (by simp [Function.surjective_id])).2 System.isRegular_nil

/-- The two-level system with the genus-two levels `[x₁, y₁][x₂, y₂] = 1` and
`[u₁, v₁][u₂, v₂] = 1` in disjoint variables is regular. -/
theorem isRegular_two_genusTwo_levels :
    (System.cons (System.cons (G := G) .nil (Fin 2 ⊕ Fin 2)
      (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
        (by simp [Function.injective_id])))) (Fin 2 ⊕ Fin 2)
      (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
        (by simp [Function.injective_id])))).IsRegular :=
  (System.isRegular_cons_genusTwo _ (by simp [Function.surjective_id])).2 isRegular_genusTwo_level

/-- The one-level system `x₁² x₂² x₃² = 1` is nondegenerate: the trivial point solves it. -/
theorem isNondegenerate_nonorientable_three_level :
    (System.cons (G := G) .nil (Fin 3)
      (.quadratic (.nonorientable 3 three_pos id Function.injective_id))).IsNondegenerate :=
  System.isNondegenerate_cons.2 ⟨System.isNondegenerate_nil, 1, by
    simp [Quadratic.Standard.toWord_def, List.ofFn_succ]⟩

/-- The one-level system `x₁² x₂² x₃² = 1`, with `κ = 3`, is not regular. -/
theorem not_isRegular_nonorientable_three_level :
    ¬(System.cons (G := G) .nil (Fin 3)
      (.quadratic (.nonorientable 3 three_pos id Function.injective_id))).IsRegular := by
  simp

/-- The two-level system with lower level `[u₁, v₁][u₂, v₂] = 1` and upper level
`[x, y] = [u₁, v₁]`, that is the standard equation `[x, y] [u₁, v₁]⁻¹ = 1`, is regular exactly when
the base group is not commutative: the coefficient `[u₁, v₁]⁻¹` of the upper level stays
nontrivial in the coordinate group of the lower level exactly then, and `x = u₁`, `y = v₁` always
solves the upper level there. -/
theorem isRegular_commutator_eq_commutator_over_genusTwo_iff :
    (System.cons (System.cons (G := G) .nil (Fin 2 ⊕ Fin 2)
      (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
        (by simp [Function.injective_id])))) (Fin 2)
      (.quadratic (.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0
        (fun j => j.elim0)
        (inr ⁅(FreeGroup.of (.inl (.inl 0)) : FreeGroup ((Fin 2 ⊕ Fin 2) ⊕ PEmpty))⁻¹,
          (FreeGroup.of (.inl (.inr 0)))⁻¹⁆⁻¹)
        ((map_ne_one_iff _ inr_injective).2 (by decide))))).IsRegular ↔
      ∃ g h : G, ¬Commute g h := by
  rw [System.isRegular_cons_quadratic, and_iff_right isRegular_genusTwo_level,
    Quadratic.Standard.isRegular_orientableCoeff_one_zero_iff]
  refine (and_iff_right ?_).trans <| (and_iff_left ?_).trans ?_
  · simp [Set.eq_univ_iff_forall, Fin.forall_fin_two]
  · exact ⟨![QuotientGroup.mk (inr (.of (.inl (.inl 0)))),
      QuotientGroup.mk (inr (.of (.inl (.inr 0))))], by
        simp [Quadratic.Standard.toWord_def, commutatorElement_def, mul_assoc]⟩
  rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_Rad]
  push Not
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v (.inl (.inr 0)), v (.inl (.inl 0)),
      by simpa [commutatorElement_eq_one_iff_commute] using hv⟩
  · -- The point `(u₁, v₁, u₂, v₂) = (g, h, h, g)` of the lower level does not kill `[u₁, v₁]`.
    rintro ⟨g, h, hgh⟩
    refine ⟨Sum.elim (Sum.elim ![g, h] ![h, g]) PEmpty.elim,
      System.mem_V_cons.2 ⟨by simp, ?_⟩, ?_⟩
    · simp [Quadratic.Standard.toWord_def, List.ofFn_succ, commutatorElement_def, mul_assoc]
    · simpa [commutatorElement_eq_one_iff_commute] using hgh ∘ Commute.symm

/-- The two-level system with lower level `[u₁, v₁][u₂, v₂] = 1` and upper level
`[x, y] [u₁, v₁][u₂, v₂] = 1` is not regular: the coefficient `[u₁, v₁][u₂, v₂]` of the upper
level is a nontrivial word, but it vanishes in the coordinate group of the lower level, over which
the upper level is the equation `[x, y] = 1`. -/
theorem not_isRegular_relator_coeff_over_genusTwo :
    ¬(System.cons (System.cons (G := G) .nil (Fin 2 ⊕ Fin 2)
      (.quadratic (.orientable 2 two_pos Sum.inl Sum.inr
        (by simp [Function.injective_id])))) (Fin 2)
      (.quadratic (.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0
        (fun j => j.elim0)
        (inr (⁅(FreeGroup.of (.inl (.inl 0)) : FreeGroup ((Fin 2 ⊕ Fin 2) ⊕ PEmpty))⁻¹,
          (FreeGroup.of (.inl (.inr 0)))⁻¹⁆ *
            ⁅(FreeGroup.of (.inl (.inl 1)) : FreeGroup ((Fin 2 ⊕ Fin 2) ⊕ PEmpty))⁻¹,
              (FreeGroup.of (.inl (.inr 1)))⁻¹⁆))
        ((map_ne_one_iff _ inr_injective).2 (by decide))))).IsRegular := fun h =>
  ((Quadratic.Standard.isRegular_orientableCoeff_one_zero_iff ..).1
    (System.isRegular_cons_quadratic.1 h).2.2).1 <|
    (QuotientGroup.eq_one_iff _).2 <| mem_Rad.2 fun v hv => by
      rw [System.mem_V_cons] at hv
      simpa [Quadratic.Standard.toWord_def, List.ofFn_succ] using hv.2

end Examples

end TauCeti.LimitGroup.NTQ
