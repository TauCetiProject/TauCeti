/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Interval
public import TauCeti.SetTheory.Ordinal.Principal
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Back-and-forth equivalence of ordinal multiples

Read as structures in the language of orders, the well-orders `ω ^ γ * δ` and `ω ^ γ * ε` are
back-and-forth equivalent at level `γ` whenever `δ` and `ε` are nonzero. At level `γ` the
back-and-forth relation cannot tell apart the number of copies of `ω ^ γ`: for instance `ω ^ 2`
and `ω ^ 2 * 2` are equivalent at level `2` without being isomorphic. This is the computation
behind the fact that a Borel complete isomorphism relation is not Borel: well-orders of types
`ω ^ β` and `ω ^ β * 2` are not isomorphic, yet they cannot be separated at level `β`.

The proof is by induction on `γ`, for all `δ` and `ε` at once, through the interval lemma. A point
`m` of a well-order of type `ω ^ (γ + 1) * δ` has initial segment of type `ω ^ γ * μ + ρ` with
`ρ < ω ^ γ`, and is answered by the point of a well-order of type `ω ^ (γ + 1) * ε` whose initial
segment has type `ω ^ γ + ρ` if `μ ≠ 0` and `ρ` otherwise. The initial segments are equivalent at
level `γ` by the induction hypothesis and the ordered-sum law, and the final segments, both of
type a nonzero multiple of `ω ^ (γ + 1)`, by the induction hypothesis.

## Main results

* `TauCeti.bfEquiv_of_type_lt_eq_omega0_opow_mul`: well-orders of types `ω ^ γ * δ` and
  `ω ^ γ * ε`, with `δ` and `ε` nonzero, are back-and-forth equivalent at level `γ`.
* `TauCeti.bfEquiv_omega0_opow_mul`: the same for the canonical well-orders
  `(ω ^ γ * δ).ToType` and `(ω ^ γ * ε).ToType`.

## References

* Antonio Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, Part 2, Lemma II.38,
  stated there for the one-sided back-and-forth relations.
-/

public section

universe u

namespace TauCeti

open FirstOrder FirstOrder.Language Fin Ordinal Order

attribute [local instance] orderStructure

/-- Well-orders of types `ω ^ γ * δ` and `ω ^ γ * ε`, with `δ` and `ε` nonzero, are back-and-forth
equivalent at level `γ`. -/
private def OmegaPowMul (γ : Ordinal.{u}) : Prop :=
  ∀ (M N : Type u) [LinearOrder M] [LinearOrder N] [WellFoundedLT M] [WellFoundedLT N]
    (δ ε : Ordinal.{u}), δ ≠ 0 → ε ≠ 0 → typeLT M = ω ^ γ * δ → typeLT N = ω ^ γ * ε →
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)

variable {M N : Type u} [LinearOrder M] [LinearOrder N] [WellFoundedLT M] [WellFoundedLT N]

/-- In a well-order of type `ω ^ (γ + 1) * δ`, the final segment above a point has type a nonzero
multiple of `ω ^ γ`. -/
private theorem exists_type_lt_Ioi_eq {γ δ : Ordinal.{u}} (hM : typeLT M = ω ^ (γ + 1) * δ)
    (m : M) : ∃ θ ≠ 0, typeLT (Set.Ioi m) = ω ^ γ * θ := by
  -- The final segment is nonempty, as `ω ^ (γ + 1) * δ` is a limit ordinal.
  have hlim : IsSuccLimit (typeLT M) := by
    have hδ : δ ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hM
      exact (type_eq_zero_iff_isEmpty.1 hM).false m
    rw [hM]
    exact isSuccLimit_mul_left (isSuccLimit_opow_left isSuccLimit_omega0
      (pos_of_gt (lt_add_one γ)).ne')
      (pos_iff_ne_zero.2 hδ)
  -- So `M` has no maximum.
  have hne : Nonempty (Set.Ioi m) :=
    let ⟨n, hn⟩ := (isSuccPrelimit_type_lt_iff.1 hlim.isSuccPrelimit).exists_gt m
    ⟨⟨n, hn⟩⟩
  -- The final segment of a multiple of the additively principal `ω ^ (γ + 1)` is a multiple.
  obtain ⟨θ, hθ⟩ := (isPrincipal_add_omega0_opow (γ + 1)).dvd_type_lt_Ioi
    (hM ▸ dvd_mul_right _ _) m
  refine ⟨ω * θ, mul_ne_zero omega0_ne_zero ?_, by rw [hθ, opow_add_one, mul_assoc]⟩
  rintro rfl
  rw [mul_zero] at hθ
  exact type_ne_zero_of_nonempty _ hθ

/-- The forth step at level `γ + 1` between well-orders of types `ω ^ (γ + 1) * δ` and
`ω ^ (γ + 1) * ε`, given the statement at level `γ`. -/
private theorem OmegaPowMul.forth {γ : Ordinal.{u}} (ih : OmegaPowMul γ) {δ ε : Ordinal.{u}}
    (hε : ε ≠ 0) (hM : typeLT M = ω ^ (γ + 1) * δ) (hN : typeLT N = ω ^ (γ + 1) * ε) (m : M) :
    ∃ n : N, BFEquiv (L := Language.order) γ 1 (snoc (Fin.elim0 : Fin 0 → M) m)
      (snoc (Fin.elim0 : Fin 0 → N) n) := by
  have hγ : ω ^ γ ≠ 0 := opow_ne_zero γ omega0_ne_zero
  -- Write the type of the initial segment below `m` as `ω ^ γ * μ + ρ` with `ρ < ω ^ γ`.
  set μ := Ordinal.typein (α := M) (· < ·) m / ω ^ γ
  set ρ := Ordinal.typein (α := M) (· < ·) m % ω ^ γ
  have hm : typeLT (Set.Iio m) = ω ^ γ * μ + ρ := by
    rw [type_Iio_lt]
    exact (div_add_mod _ _).symm
  -- Answer by the point `n` whose initial segment has type `ω ^ γ + ρ` if `μ ≠ 0`, `ρ` otherwise.
  have hlt : ω ^ γ + ρ < typeLT N := by
    rw [hN]
    refine lt_of_lt_of_le (isPrincipal_add_omega0_opow (γ + 1)
      ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one γ))
      ((mod_lt _ hγ).trans ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one γ)))) ?_
    exact le_mul_left _ (pos_iff_ne_zero.2 hε)
  have hν : (if μ = 0 then ρ else ω ^ γ + ρ) < typeLT N := by
    split_ifs
    · exact le_add_self.trans_lt hlt
    · exact hlt
  refine ⟨Ordinal.enum (· < ·) ⟨_, hν⟩, (bfEquiv_snoc_elim0_iff γ _ _).2 ⟨?_, ?_⟩⟩
  · have hn : typeLT (Set.Iio (Ordinal.enum (α := N) (· < ·) ⟨_, hν⟩)) =
        if μ = 0 then ρ else ω ^ γ + ρ := by
      rw [type_Iio_lt, typein_enum]
    split_ifs at hn with hμ
    · exact bfEquiv_of_type_lt_eq (by rw [hm, hn, hμ, mul_zero, zero_add]) γ
    · -- Both initial segments are ordered sums of a nonzero multiple of `ω ^ γ` and `ρ`.
      refine (bfEquiv_of_type_lt_eq (B := (ω ^ γ * μ).ToType ⊕ₗ ρ.ToType)
        (by rw [hm, type_lt_sum_lex, type_toType, type_toType]) γ).trans <|
        (BFEquiv.trans ?_ (bfEquiv_of_type_lt_eq (A := (ω ^ γ * 1).ToType ⊕ₗ ρ.ToType)
          (by rw [hn, type_lt_sum_lex, type_toType, type_toType, mul_one]) γ))
      exact BFEquiv.sumLex (ih _ _ μ 1 hμ one_ne_zero (type_toType _) (type_toType _))
        (BFEquiv.refl γ _)
  · obtain ⟨θ, hθ, hθm⟩ := exists_type_lt_Ioi_eq hM m
    obtain ⟨θ', hθ', hθn⟩ := exists_type_lt_Ioi_eq hN (Ordinal.enum (· < ·) ⟨_, hν⟩)
    exact ih _ _ θ θ' hθ hθ' hθm hθn

/-- The statement for all levels, by induction on the level. -/
private theorem omegaPowMul (γ : Ordinal.{u}) : OmegaPowMul γ := by
  induction γ using Ordinal.limitRecOn with
  | zero =>
    intro M N _ _ _ _ _ _ _ _ _ _
    exact BFEquiv.zero.2 sameAtomicType_elim0
  | add_one γ ih =>
    intro M N _ _ _ _ δ ε hδ hε hM hN
    -- At the previous level, both are nonzero multiples of `ω ^ γ`.
    have hM' : typeLT M = ω ^ γ * (ω * δ) := by rw [hM, opow_add_one, mul_assoc]
    have hN' : typeLT N = ω ^ γ * (ω * ε) := by rw [hN, opow_add_one, mul_assoc]
    refine (BFEquiv.add_one γ _ _).2 ⟨ih M N _ _ (mul_ne_zero omega0_ne_zero hδ)
      (mul_ne_zero omega0_ne_zero hε) hM' hN', fun m => ?_, fun n => ?_⟩
    · exact ih.forth hε hM hN m
    · exact (ih.forth hδ hN hM n).imp fun _ h => h.symm
  | limit γ hγ ih =>
    intro M N _ _ _ _ δ ε hδ hε hM hN
    -- Below a limit level `γ`, a multiple of `ω ^ γ` is a multiple of `ω ^ β` for every `β < γ`.
    refine (BFEquiv.limit hγ _ _).2 fun β hβ => ih β hβ M N (ω ^ (γ - β) * δ) (ω ^ (γ - β) * ε)
      (mul_ne_zero (opow_ne_zero _ omega0_ne_zero) hδ)
      (mul_ne_zero (opow_ne_zero _ omega0_ne_zero) hε) ?_ ?_
    · rw [hM, ← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le hβ.le]
    · rw [hN, ← mul_assoc, ← opow_add, Ordinal.add_sub_cancel_of_le hβ.le]

/-- **Ordinal multiples at level `γ`.** Well-orders of types `ω ^ γ * δ` and `ω ^ γ * ε`, with `δ`
and `ε` nonzero, are back-and-forth equivalent at level `γ` as structures in the language of
orders. -/
theorem bfEquiv_of_type_lt_eq_omega0_opow_mul {γ δ ε : Ordinal.{u}} (hδ : δ ≠ 0) (hε : ε ≠ 0)
    (hM : typeLT M = ω ^ γ * δ) (hN : typeLT N = ω ^ γ * ε) :
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  omegaPowMul γ M N δ ε hδ hε hM hN

/-- **Ordinal multiples at level `γ`.** For nonzero `δ` and `ε`, the well-orders
`(ω ^ γ * δ).ToType` and `(ω ^ γ * ε).ToType` are back-and-forth equivalent at level `γ` as
structures in the language of orders. -/
theorem bfEquiv_omega0_opow_mul (γ : Ordinal.{u}) {δ ε : Ordinal.{u}} (hδ : δ ≠ 0)
    (hε : ε ≠ 0) :
    BFEquiv (L := Language.order) γ 0 (Fin.elim0 : Fin 0 → (ω ^ γ * δ).ToType)
      (Fin.elim0 : Fin 0 → (ω ^ γ * ε).ToType) :=
  bfEquiv_of_type_lt_eq_omega0_opow_mul hδ hε (type_toType _) (type_toType _)

end TauCeti
