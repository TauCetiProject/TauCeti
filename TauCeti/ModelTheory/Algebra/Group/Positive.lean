/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.MalcevEquation
public import TauCeti.Logic.ForallExistsAlt
public import TauCeti.ModelTheory.Algebra.Group.TermWord
public import TauCeti.ModelTheory.Positive
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.FreeGroup.CSA
import TauCeti.GroupTheory.FreeGroup.Vaught

/-!
# Positive group formulas as single equations

Let `𝒯` be the class of torsion-free CSA groups satisfying Vaught's condition, with two
distinguished coefficients `a`, `b` that do not commute; it contains the nonabelian free groups.
Over the groups of `𝒯`, Malcev's word turns a conjunction of two equations into one equation and
a companion word does the same for a disjunction. Hence every positive quantifier-free formula
of the group language with coefficients is equivalent, uniformly over `𝒯`, to a single equation
`w = 1`, and every positive formula is equivalent to an alternation of quantifiers
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1}` in front of a single equation. Quantifiers that are missing
from the strict alternation are supplied by variables that do not occur in the equation.

## Main results

* `FirstOrder.Language.group.exists_word_realize_iff_of_isPositive_of_isQF`: a positive
  quantifier-free formula is equivalent over `𝒯` to a single equation.
* `FirstOrder.Language.group.exists_word_realize_iff_forallExistsAlt`: a positive formula is
  equivalent over `𝒯` to an alternation of quantifiers in front of a single equation.
* `FirstOrder.Language.group.exists_word_realize_sentence_iff_forallExistsAlt`: the same for
  positive sentences.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.3, §3.1 (Corollaries 3, 5 and 6), §3.3 (Lemma 9) and §4.4.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemmas 3–4.
-/

public section

namespace FirstOrder.Language.group

open FirstOrder TauCeti _root_.Group

universe u

variable {X A : Type*} {n : ℕ}

/-- **Kharlampovich–Myasnikov, Corollary 6.** A positive quantifier-free formula of the group
language with coefficients is equivalent to a single equation `w = 1`, in every torsion-free CSA
group satisfying Vaught's condition in which the coefficients `a` and `b` do not commute. The
word `w` does not depend on the group. -/
theorem exists_word_realize_iff_of_isPositive_of_isQF
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsPositive) (hqf : φ.IsQF) (a b : A) :
    ∃ w : FreeGroup ((X ⊕ Fin n) ⊕ A),
      ∀ (G : Type*) [Group G] [IsMulTorsionFree G] (v : X → G) (c : A → G) (xs : Fin n → G),
        IsVaught G → IsCSA G → ¬Commute (c a) (c b) →
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        (φ.Realize v xs ↔ FreeGroup.lift (Sum.elim (Sum.elim v xs) c) w = 1) := by
  apply hφ.induction_on_isQF hqf
  · intro ψ h
    cases h with
    | equal t s =>
      exact ⟨Term.toWord t * (Term.toWord s)⁻¹, fun G _ _ v c xs _ _ _ =>
        Term.realize_equal_iff c (Sum.elim v xs) t s⟩
    | rel R _ =>
      -- The coefficient extension has two empty relation-symbol summands.
      change Empty ⊕ Empty at R
      exact R.elim isEmptyElim isEmptyElim
  · rintro ψ₁ ψ₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    refine ⟨malcevWord (.of (.inr a)) (.of (.inr b)) w₁ w₂, fun G _ _ v c xs hV hG hab => ?_⟩
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    rw [BoundedFormula.realize_inf, h₁ G v c xs hV hG hab, h₂ G v c xs hV hG hab, map_malcevWord]
    simpa using (hV.malcevWord_eq_one_iff hG hab).symm
  · rintro ψ₁ ψ₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    refine ⟨malcevOrWord (.of (.inr a)) (.of (.inr b)) w₁ w₂, fun G _ _ v c xs hV hG hab => ?_⟩
    let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
    let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
    rw [BoundedFormula.realize_sup, h₁ G v c xs hV hG hab, h₂ G v c xs hV hG hab,
      map_malcevOrWord]
    simpa using (hV.malcevOrWord_eq_one_iff hG hab).symm

/-- Reindex the last bound slot of `Fin (n + 1)` as the first quantified variable `z` of an
alternation of length `k + 1`, shifting the other quantified variables up by one. -/
private def quantSlot (X : Type*) (n k : ℕ) (z : Fin (k + 1) ⊕ Fin (k + 1)) :
    (X ⊕ Fin (n + 1)) ⊕ (Fin k ⊕ Fin k) → (X ⊕ Fin n) ⊕ (Fin (k + 1) ⊕ Fin (k + 1)) :=
  Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) (Fin.lastCases (Sum.inr z) (Sum.inl ∘ Sum.inr)))
    (Sum.inr ∘ Sum.map Fin.succ Fin.succ)

/-- Evaluating a word relabelled along `quantSlot` reads the last bound slot off the quantified
variable `z`. -/
private theorem lift_map_quantSlot {G : Type*} [Group G] {k : ℕ} (v : X → G) (c : A → G)
    (xs : Fin n → G) (x y : G) (xs' ys' : Fin k → G) (z : Fin (k + 1) ⊕ Fin (k + 1))
    (w : FreeGroup (((X ⊕ Fin (n + 1)) ⊕ (Fin k ⊕ Fin k)) ⊕ A)) :
    FreeGroup.lift (Sum.elim (Sum.elim (Sum.elim v xs)
        (Sum.elim (Fin.cons x xs') (Fin.cons y ys'))) c)
      (FreeGroup.map (Sum.map (quantSlot X n k z) id) w) =
    FreeGroup.lift (Sum.elim (Sum.elim (Sum.elim v
        (Fin.snoc xs (Sum.elim (Fin.cons x xs') (Fin.cons y ys') z))) (Sum.elim xs' ys')) c) w := by
  rw [FreeGroup.lift_map, Sum.elim_comp_map, Function.comp_id]
  congr 3
  funext i
  rcases i with (i | i) | i | i
  · rfl
  · induction i using Fin.lastCases <;> simp [quantSlot]
  · simp [quantSlot]
  · simp [quantSlot]

/-- A positive formula in prenex form is equivalent to an alternation of quantifiers in front
of a single equation: each quantifier of the prefix becomes one pair `∀ x ∃ y` in which the
other variable does not occur in the equation. -/
private theorem exists_word_realize_iff_forallExistsAlt_of_isPrenex
    {φ : Language.group[[A]].BoundedFormula X n} (hp : φ.IsPrenex) (hφ : φ.IsPositive)
    (a b : A) :
    ∃ (k : ℕ) (w : FreeGroup (((X ⊕ Fin n) ⊕ (Fin k ⊕ Fin k)) ⊕ A)),
      ∀ (G : Type*) [Group G] [IsMulTorsionFree G] (v : X → G) (c : A → G) (xs : Fin n → G),
        IsVaught G → IsCSA G → ¬Commute (c a) (c b) →
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        (φ.Realize v xs ↔ ForallExistsAlt k fun x y : Fin k → G =>
          FreeGroup.lift (Sum.elim (Sum.elim (Sum.elim v xs) (Sum.elim x y)) c) w = 1) := by
  apply hp.induction_on_isPositive hφ
  · intro m θ hqf hθ
    obtain ⟨w, h⟩ := exists_word_realize_iff_of_isPositive_of_isQF hθ hqf a b
    refine ⟨0, FreeGroup.map (Sum.map Sum.inl id) w, fun G _ _ v c xs hV hG hab => ?_⟩
    rw [h G v c xs hV hG hab, forallExistsAlt_zero, FreeGroup.lift_map, Sum.elim_comp_map,
      Function.comp_id, Sum.elim_comp_inl]
  · rintro m θ ⟨k, w, h⟩
    refine ⟨k + 1, FreeGroup.map (Sum.map (quantSlot X m k (.inl 0)) id) w,
      fun G _ _ v c xs hV hG hab => ?_⟩
    -- A universal quantifier is `∀ x ∃ y` with `y` not occurring.
    simp only [BoundedFormula.realize_all, forallExistsAlt_succ, lift_map_quantSlot,
      Sum.elim_inl, Fin.cons_zero, exists_const]
    exact forall_congr' fun t => h G v c (Fin.snoc xs t) hV hG hab
  · rintro m θ ⟨k, w, h⟩
    refine ⟨k + 1, FreeGroup.map (Sum.map (quantSlot X m k (.inr 0)) id) w,
      fun G _ _ v c xs hV hG hab => ?_⟩
    -- An existential quantifier is `∀ x ∃ y` with `x` not occurring; a group is nonempty.
    simp only [BoundedFormula.realize_ex, forallExistsAlt_succ, lift_map_quantSlot,
      Sum.elim_inr, Fin.cons_zero, forall_const]
    exact exists_congr fun t => h G v c (Fin.snoc xs t) hV hG hab

/-- **Kharlampovich–Myasnikov, Lemma 9 and §4.4.** A positive formula of the group language with
coefficients is equivalent to `∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (w = 1)` for a single word `w`, in
every torsion-free CSA group satisfying Vaught's condition in which the coefficients `a` and `b`
do not commute. The number `k` and the word `w` do not depend on the group. In `w` the free
variables and the bound-variable slots are the letters `Sum.inl (Sum.inl _)`, the quantified
variables are `x i = Sum.inl (Sum.inr (Sum.inl i))` and `y i = Sum.inl (Sum.inr (Sum.inr i))`,
and the coefficients are the letters `Sum.inr _`. -/
theorem exists_word_realize_iff_forallExistsAlt
    {φ : Language.group[[A]].BoundedFormula X n} (hφ : φ.IsPositive) (a b : A) :
    ∃ (k : ℕ) (w : FreeGroup (((X ⊕ Fin n) ⊕ (Fin k ⊕ Fin k)) ⊕ A)),
      ∀ (G : Type*) [Group G] [IsMulTorsionFree G] (v : X → G) (c : A → G) (xs : Fin n → G),
        IsVaught G → IsCSA G → ¬Commute (c a) (c b) →
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        (φ.Realize v xs ↔ ForallExistsAlt k fun x y : Fin k → G =>
          FreeGroup.lift (Sum.elim (Sum.elim (Sum.elim v xs) (Sum.elim x y)) c) w = 1) := by
  obtain ⟨ψ, hp, hψ, e⟩ := hφ.exists_isPrenex_and_isPositive_and_theoryIff
  obtain ⟨k, w, h⟩ := exists_word_realize_iff_forallExistsAlt_of_isPrenex hp hψ a b
  refine ⟨k, w, fun G _ _ v c xs hV hG hab => ?_⟩
  let : Language.group.Structure G := TauCeti.Group.structureOfGroup G
  let : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
  exact e.realize_bd_iff.trans (h G v c xs hV hG hab)

/-- A positive sentence of the group language with coefficients is equivalent to
`∀ x₀ ∃ y₀ … ∀ x_{k-1} ∃ y_{k-1} (w = 1)` for a single word `w` in the variables
`x i = Sum.inl (Sum.inl i)`, `y i = Sum.inl (Sum.inr i)` and the coefficients, in every
torsion-free CSA group satisfying Vaught's condition in which the coefficients `a` and `b` do
not commute. -/
theorem exists_word_realize_sentence_iff_forallExistsAlt
    {σ : Language.group[[A]].Sentence} (hσ : σ.IsPositive) (a b : A) :
    ∃ (k : ℕ) (w : FreeGroup ((Fin k ⊕ Fin k) ⊕ A)),
      ∀ (G : Type*) [Group G] [IsMulTorsionFree G] (c : A → G),
        IsVaught G → IsCSA G → ¬Commute (c a) (c b) →
        letI : Language.group.Structure G := TauCeti.Group.structureOfGroup G
        letI : (Language.constantsOn A).Structure G := Language.constantsOn.structure c
        (G ⊨ σ ↔ ForallExistsAlt k fun x y : Fin k → G =>
          FreeGroup.lift (Sum.elim (Sum.elim x y) c) w = 1) := by
  obtain ⟨k, w, h⟩ := exists_word_realize_iff_forallExistsAlt hσ a b
  refine ⟨k, FreeGroup.map (Sum.map (Sum.elim (Sum.elim Empty.elim Fin.elim0) id) id) w,
    fun G _ _ c hV hG hab => (h G default c default hV hG hab).trans ?_⟩
  have hcomp (x y : Fin k → G) : Sum.elim x y ∘ Sum.elim (Sum.elim Empty.elim Fin.elim0) id =
      Sum.elim (Sum.elim default default) (Sum.elim x y) := by
    funext i
    rcases i with (i | i) | i
    · exact i.elim
    · exact i.elim0
    · rfl
  simp only [FreeGroup.lift_map, Sum.elim_comp_map, Function.comp_id, hcomp]

/-- A free group on at least two letters, with the letters as coefficients, is a torsion-free CSA
group satisfying Vaught's condition in which two distinct letters do not commute: every positive
sentence is equivalent in it to an alternation of quantifiers in front of a single equation. -/
example {A : Type u} {σ : Language.group[[A]].Sentence} (hσ : σ.IsPositive) {a b : A}
    (hab : a ≠ b) :
    ∃ (k : ℕ) (w : FreeGroup ((Fin k ⊕ Fin k) ⊕ A)),
      letI : Language.group.Structure (FreeGroup A) := TauCeti.Group.structureOfGroup _
      letI : (Language.constantsOn A).Structure (FreeGroup A) :=
        Language.constantsOn.structure FreeGroup.of
      (FreeGroup A ⊨ σ ↔ ForallExistsAlt k fun x y : Fin k → FreeGroup A =>
        FreeGroup.lift (Sum.elim (Sum.elim x y) FreeGroup.of) w = 1) := by
  obtain ⟨k, w, h⟩ := exists_word_realize_sentence_iff_forallExistsAlt.{u, u} hσ a b
  exact ⟨k, w, h (FreeGroup A) FreeGroup.of IsFreeGroup.isVaught IsFreeGroup.isCSA
    fun h => hab (FreeGroup.eq_of_commute_of_of h)⟩

end FirstOrder.Language.group
