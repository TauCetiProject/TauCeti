/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.ProperQuotient
public import TauCeti.GroupTheory.FreeGroup.GenEq.SolutionTree.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Monotone
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.SuccPred.Fin
import Mathlib.Tactic.FinCases

/-!
# Parametric covers and the gluing of decomposition trees

Let `Ω` be a parametric generalised equation over a free group `F = F(A)`. Kharlampovich and
Myasnikov (§5.6, Theorem 5) build a finite tree `T_sol(Ω, Λ)` whose terminal vertices carry
generalised equations `Ω_v` such that every solution `U` of `Ω` is the composite
`U = U_v ∘ σ_n ∘ π_n ∘ ⋯ ∘ π_1 ∘ σ_0` of a solution `U_v` of a terminal equation, the canonical
epimorphisms `π_i` of the edges of a branch and canonical automorphisms `σ_i` of the coordinate
groups along it; the canonical automorphisms fix the parametric items and the epimorphisms send
each parametric item to a product of consecutive parametric items, so that the values of the
parameters are fixed words in the items of the terminal equation, reduced as written.

We record what this construction gives for solutions. A *parametric cover* of `Ω`
(`TauCeti.ParamGenEq.IsParamCover`) is a finite family of parametric generalised equations `T j`
with, for each `j`, a map `bd j` from the boundaries of `Ω` to those of `T j`, such that every
parametric item `k` of `Ω` is sent to the segment between `bd j k` and `bd j (k + 1)`, which is
nonempty and consists of parametric items, the parametric items of `T j` all arising in this way,
and every solution `U` of `Ω` is `U' ∘ Φ` for a solution `U'` of some `T j` and an
`F(A)`-homomorphism `Φ` of coordinate groups sending each parametric item to its segment; the
segment, evaluated at `U'`, is the word of `U` at that item letter by letter. Unlike a
transformation (`TauCeti.GenEq.Transformation`), a cover does not fix one homomorphism per member:
`Φ` depends on the solution, as the canonical automorphisms along a branch do.

A parametric generalised equation covers itself, and covers compose: if the members of a cover of
`Ω` have covers, the composite family covers `Ω`. Gluing decomposition trees at the leaves whose
coordinate groups are proper quotients terminates because there is no infinite descending chain of
proper quotients of coordinate groups (`TauCeti.GenEq.wellFounded_isProperQuotient`); this replaces
the source's argument by König's lemma. The result is `TauCeti.ParamGenEq.hasParamCover_of_forall`:
if every parametric generalised equation has a cover by equations each of which has a property `p`
or has as coordinate group a proper quotient of its own, then every parametric generalised
equation has a cover by equations with the property `p`. For the equation `y = x` with parameter
`x`, one terminal equation, the parameter section alone, covers the solutions (examples at the end
of the file).

## Main definitions

* `TauCeti.ParamGenEq.IsParamCover`: a finite family of equations covering the solutions of `Ω`,
  with the parametric items sent to segments of parametric items.
* `TauCeti.ParamGenEq.HasParamCover`: `Ω` has a parametric cover by equations with a property.

## Main results

* `TauCeti.ParamGenEq.hasParamCover_self`: an equation with the property `p` covers itself.
* `TauCeti.ParamGenEq.HasParamCover.bind`: parametric covers compose.
* `TauCeti.ParamGenEq.hasParamCover_of_forall`: gluing decomposition trees at the leaves whose
  coordinate groups are proper quotients.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.6, Theorem 5.
-/

public section

namespace TauCeti

namespace ParamGenEq

open GroupAlgGeom FreeGroup Monoid.Coprod

variable {A : Type*}

/-- The equations `T j`, with the maps `bd j` on boundaries, form a parametric cover of `Ω`: each
parametric item `k` of `Ω` goes to the nonempty segment of `T j` between `bd j k` and
`bd j (k + 1)`, all of whose items are parametric, every parametric item of `T j` lying in such a
segment; and every solution `U` of `Ω` is the composite of a solution `U'` of some `T j` with an
`F(A)`-homomorphism `Φ` of coordinate groups that sends each parametric item to its segment, the
segment evaluated at `U'` being the word of `U` at that item letter by letter. -/
structure IsParamCover (Ω : ParamGenEq A) {n : ℕ} (T : Fin n → ParamGenEq A)
    (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)) : Prop where
  /-- The segment of a parametric item is nonempty. -/
  lt : ∀ j k, Ω.IsParamItem k → bd j k.castSucc < bd j k.succ
  /-- The segment of a parametric item consists of parametric items. -/
  isParamItem : ∀ j k, Ω.IsParamItem k → ∀ k' : Fin (T j).numItems,
    bd j k.castSucc ≤ k'.castSucc → k'.succ ≤ bd j k.succ → (T j).IsParamItem k'
  /-- Every parametric item of a member of the family lies in the segment of a parametric item of
  `Ω`. -/
  exists_isParamItem : ∀ j (k' : Fin (T j).numItems), (T j).IsParamItem k' →
    ∃ k, Ω.IsParamItem k ∧ bd j k.castSucc ≤ k'.castSucc ∧ k'.succ ≤ bd j k.succ
  /-- Every solution factors through a solution of a member of the family, the parametric items
  going to their segments. -/
  exists_factor : ∀ U : Ω.Solution, ∃ (j : Fin n) (Φ : GenEq.CoordHom Ω.toGenEq (T j).toGenEq)
      (U' : (T j).Solution), U'.toHom.comp Φ = U.toHom ∧
      (∀ k, Ω.IsParamItem k →
        Φ (Ω.item k) = (T j).wordElem ((T j).segment (bd j k.castSucc) (bd j k.succ) true)) ∧
      ∀ k, Ω.IsParamItem k →
        substituteVars U'.word ((T j).segment (bd j k.castSucc) (bd j k.succ) true) = U.word k

/-- `Ω` has a parametric cover by finitely many equations with the property `p`. -/
def HasParamCover (Ω : ParamGenEq A) (p : ParamGenEq A → Prop) : Prop :=
  ∃ (n : ℕ) (T : Fin n → ParamGenEq A)
    (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)),
    Ω.IsParamCover T bd ∧ ∀ j, p (T j)

theorem hasParamCover_iff {Ω : ParamGenEq A} {p : ParamGenEq A → Prop} :
    Ω.HasParamCover p ↔ ∃ (n : ℕ) (T : Fin n → ParamGenEq A)
      (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)),
      Ω.IsParamCover T bd ∧ ∀ j, p (T j) :=
  Iff.rfl

/-! ### Covers of an equation by itself, and composition of covers -/

-- Every parametric generalised equation covers itself, each parametric item going to itself.
private theorem isParamCover_self (Ω : ParamGenEq A) :
    Ω.IsParamCover (fun _ : Fin 1 => Ω) fun _ => id where
  lt _ k _ := k.castSucc_lt_succ
  isParamItem _ k hk k' h₁ h₂ := by
    rwa [le_antisymm (Fin.succ_le_succ_iff.1 h₂) (Fin.castSucc_le_castSucc_iff.1 h₁)]
  exists_isParamItem _ k' hk' := ⟨k', hk', le_rfl, le_rfl⟩
  exists_factor U := ⟨0, GHom.id _, U, GHom.comp_id _, fun k _ => by simp, fun k _ => by simp⟩

-- Concatenation of segments: if each item `k` of `T` between the boundaries `a` and `b` has the
-- value of the segment of `S` between `g k` and `g (k + 1)`, for a pair of maps on words turning
-- concatenation into multiplication, then the segment of `T` between `a` and `b` has the value
-- of the segment of `S` between `g a` and `g b`.
private theorem map_segment_eq {β : Type*} [Monoid β] {T S : GenEq A}
    (F : List ((Fin T.numItems ⊕ A) × Bool) → β) (G : List ((Fin S.numItems ⊕ A) × Bool) → β)
    (hF : ∀ x y, F (x ++ y) = F x * F y) (hG : ∀ x y, G (x ++ y) = G x * G y) (hF₀ : F [] = 1)
    (hG₀ : G [] = 1) {g : Fin (T.numItems + 1) → Fin (S.numItems + 1)} {a : Fin (T.numItems + 1)} :
    ∀ b, a ≤ b → MonotoneOn g (Set.Icc a b) → (∀ k : Fin T.numItems, a ≤ k.castSucc → k.succ ≤ b →
      F [(Sum.inl k, true)] = G (S.segment (g k.castSucc) (g k.succ) true)) →
    F (T.segment a b true) = G (S.segment (g a) (g b) true) := by
  intro b
  induction b using Fin.induction with
  | zero =>
    intro hab _ _
    obtain rfl := le_antisymm hab (Fin.zero_le _)
    simp [GenEq.segment_eq_nil_of_le, hF₀, hG₀]
  | succ i ih =>
    intro hab hg h
    rcases hab.lt_or_eq with hab | rfl
    · rw [← Fin.le_castSucc_iff] at hab
      have hi := i.castSucc_lt_succ.le
      rw [← S.segment_append (hg ⟨le_rfl, hab.trans hi⟩ ⟨hab, hi⟩ hab)
          (hg ⟨hab, hi⟩ ⟨hab.trans hi, le_rfl⟩ hi), ← T.segment_append hab hi,
        hF, hG, ih hab (MonotoneOn.mono hg (Set.Icc_subset_Icc_right hi)) fun k hk₁ hk₂ =>
          h k hk₁ (hk₂.trans hi), ← h i hab le_rfl]
      congr 2
      simp
    · simp [GenEq.segment_eq_nil_of_le, hF₀, hG₀]

section Comp

/-! Composing a cover `(T, bd)` of `Ω` with a cover `(S, bd')` of one of its members `T j`. -/

variable {Ω : ParamGenEq A} {n : ℕ} {T : Fin n → ParamGenEq A}
  {bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)} {j : Fin n} {m : ℕ}
  {S : Fin m → ParamGenEq A} {bd' : ∀ t, Fin ((T j).numItems + 1) → Fin ((S t).numItems + 1)}
  (hT : Ω.IsParamCover T bd) (hS : (T j).IsParamCover S bd') (t : Fin m)
include hT hS

-- On the segment of a parametric item of `Ω`, the boundary map `bd' t` is strictly increasing,
-- since the items of the segment are parametric and have nonempty segments in `S t`.
private theorem IsParamCover.strictMonoOn_comp {k : Fin Ω.numItems} (hk : Ω.IsParamItem k) :
    StrictMonoOn (bd' t) (Set.Icc (bd j k.castSucc) (bd j k.succ)) := by
  refine strictMonoOn_of_lt_succ Set.ordConnected_Icc fun x hx ha hb => ?_
  induction x using Fin.lastCases with
  | last => exact absurd (fun y _ => Fin.le_last y) hx
  | cast k' =>
    rw [Fin.orderSucc_castSucc] at hb ⊢
    exact hS.lt t k' (hT.isParamItem j k hk k' ha.1 hb.2)

private theorem IsParamCover.lt_comp (k : Fin Ω.numItems) (hk : Ω.IsParamItem k) :
    bd' t (bd j k.castSucc) < bd' t (bd j k.succ) :=
  have hab := hT.lt j k hk
  hT.strictMonoOn_comp hS t hk ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab

private theorem IsParamCover.isParamItem_comp (k : Fin Ω.numItems) (hk : Ω.IsParamItem k)
    (k'' : Fin (S t).numItems) (h₁ : bd' t (bd j k.castSucc) ≤ k''.castSucc)
    (h₂ : k''.succ ≤ bd' t (bd j k.succ)) : (S t).IsParamItem k'' := by
  -- For every boundary `b` of the segment of `k` with `k''` to the left of `bd' t b`, the item
  -- `k''` lies in the segment of an item of `T j` between `bd j k` and `b`: induction on `b`.
  suffices ∀ b, bd j k.castSucc ≤ b → b ≤ bd j k.succ → k''.succ ≤ bd' t b →
      (S t).IsParamItem k'' from this _ (hT.lt j k hk).le le_rfl h₂
  have hlt : ¬ k''.succ ≤ bd' t (bd j k.castSucc) := fun h =>
    (h.trans h₁).not_gt k''.castSucc_lt_succ
  intro b
  induction b using Fin.induction with
  | zero => exact fun hab _ hb => absurd (le_antisymm hab (Fin.zero_le _) ▸ hb) hlt
  | succ i ih =>
    intro hab hb hk''
    rcases hab.lt_or_eq with hab | hab
    · rw [← Fin.le_castSucc_iff] at hab
      by_cases hi : k''.succ ≤ bd' t i.castSucc
      · exact ih hab (i.castSucc_lt_succ.le.trans hb) hi
      · exact hS.isParamItem t i (hT.isParamItem j k hk i hab hb) k''
          (Fin.le_castSucc_iff.2 (not_le.1 hi)) hk''
    · exact absurd (hab ▸ hk'') hlt

private theorem IsParamCover.exists_isParamItem_comp (k'' : Fin (S t).numItems)
    (hk'' : (S t).IsParamItem k'') : ∃ k, Ω.IsParamItem k ∧ bd' t (bd j k.castSucc) ≤ k''.castSucc ∧
      k''.succ ≤ bd' t (bd j k.succ) := by
  obtain ⟨k', hk', h₁, h₂⟩ := hS.exists_isParamItem t k'' hk''
  obtain ⟨k, hk, h₃, h₄⟩ := hT.exists_isParamItem j k' hk'
  have hmono := (hT.strictMonoOn_comp hS t hk).monotoneOn
  have hk' := k'.castSucc_lt_succ.le
  have hab := (hT.lt j k hk).le
  exact ⟨k, hk, (hmono ⟨le_rfl, hab⟩ ⟨h₃, hk'.trans h₄⟩ h₃).trans h₁,
    h₂.trans (hmono ⟨h₃.trans hk', h₄⟩ ⟨hab, le_rfl⟩ h₄)⟩

private theorem IsParamCover.wordElem_comp {Ψ : GenEq.CoordHom (T j).toGenEq (S t).toGenEq}
    (hΨ : ∀ k', (T j).IsParamItem k' →
      Ψ ((T j).item k') = (S t).wordElem ((S t).segment (bd' t k'.castSucc) (bd' t k'.succ) true))
    {k : Fin Ω.numItems} (hk : Ω.IsParamItem k) :
    Ψ ((T j).wordElem ((T j).segment (bd j k.castSucc) (bd j k.succ) true)) =
      (S t).wordElem ((S t).segment (bd' t (bd j k.castSucc)) (bd' t (bd j k.succ)) true) :=
  map_segment_eq (fun w => Ψ ((T j).wordElem w)) (S t).wordElem (by simp) (by simp) (by simp)
    (by simp) _ (hT.lt j k hk).le (hT.strictMonoOn_comp hS t hk).monotoneOn fun k' h₁ h₂ => by
      simpa using hΨ k' (hT.isParamItem j k hk k' h₁ h₂)

private theorem IsParamCover.substituteVars_comp {U' : (T j).Solution} {U'' : (S t).Solution}
    (hw : ∀ k', (T j).IsParamItem k' → substituteVars U''.word
      ((S t).segment (bd' t k'.castSucc) (bd' t k'.succ) true) = U'.word k') {k : Fin Ω.numItems}
    (hk : Ω.IsParamItem k) :
    substituteVars U''.word ((S t).segment (bd' t (bd j k.castSucc)) (bd' t (bd j k.succ)) true) =
      substituteVars U'.word ((T j).segment (bd j k.castSucc) (bd j k.succ) true) :=
  congrArg FreeMonoid.toList (map_segment_eq
    (fun w => FreeMonoid.ofList (substituteVars U'.word w))
    (fun w => FreeMonoid.ofList (substituteVars U''.word w)) (by simp [substituteVars_append])
    (by simp [substituteVars_append]) (by simp) (by simp) _ (hT.lt j k hk).le
    (hT.strictMonoOn_comp hS t hk).monotoneOn fun k' h₁ h₂ => by
      simp [hw k' (hT.isParamItem j k hk k' h₁ h₂)]).symm

end Comp

-- Composition of covers: the members of covers of the members of a cover of `Ω`, indexed by
-- `Fin (∑ j, m j) ≃ Σ j, Fin (m j)`, cover `Ω`.
private theorem IsParamCover.comp {Ω : ParamGenEq A} {n : ℕ} {T : Fin n → ParamGenEq A}
    {bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)} (hT : Ω.IsParamCover T bd)
    {m : Fin n → ℕ} {S : ∀ j, Fin (m j) → ParamGenEq A}
    {bd' : ∀ j t, Fin ((T j).numItems + 1) → Fin ((S j t).numItems + 1)}
    (hS : ∀ j, (T j).IsParamCover (S j) (bd' j)) :
    Ω.IsParamCover (fun i => S (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2)
      fun i k => bd' (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2
        (bd (finSigmaFinEquiv.symm i).1 k) where
  lt i := hT.lt_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  isParamItem i := hT.isParamItem_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  exists_isParamItem i :=
    hT.exists_isParamItem_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  exists_factor U := by
    obtain ⟨j, Φ, U', hU', hΦ, hw⟩ := hT.exists_factor U
    obtain ⟨t, Ψ, U'', hU'', hΨ, hw'⟩ := (hS j).exists_factor U'
    refine ⟨finSigmaFinEquiv ⟨j, t⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    refine ⟨Ψ.comp Φ, U'', by rw [← GHom.comp_assoc, hU'', hU'], fun k hk => ?_, fun k hk => ?_⟩
    · rw [GHom.coe_comp, Function.comp_apply, hΦ k hk, hT.wordElem_comp (hS j) t hΨ hk]
    · rw [hT.substituteVars_comp (hS j) t hw' hk, hw k hk]

/-- A parametric generalised equation with the property `p` has a parametric cover by equations
with the property `p`: itself. -/
theorem hasParamCover_self {Ω : ParamGenEq A} {p : ParamGenEq A → Prop} (hp : p Ω) :
    Ω.HasParamCover p :=
  hasParamCover_iff.2 ⟨1, _, _, isParamCover_self Ω, fun _ => hp⟩

/-- Parametric covers compose: if `Ω` has a parametric cover by equations with the property `q`,
and every equation with the property `q` has a parametric cover by equations with the property
`p`, then `Ω` has a parametric cover by equations with the property `p`. -/
theorem HasParamCover.bind {Ω : ParamGenEq A} {p q : ParamGenEq A → Prop} (h : Ω.HasParamCover q)
    (hq : ∀ T, q T → T.HasParamCover p) : Ω.HasParamCover p := by
  obtain ⟨n, T, bd, hT, hqT⟩ := hasParamCover_iff.1 h
  choose m S bd' hS hpS using fun j => hq (T j) (hqT j)
  exact hasParamCover_iff.2 ⟨_, _, _, hT.comp hS, fun i => hpS _ _⟩

/-- **Gluing decomposition trees** (Kharlampovich–Myasnikov, §5.6, finiteness of `T_sol(Ω, Λ)`).
Let `p` be a property of parametric generalised equations. If every parametric generalised
equation has a parametric cover by equations that have the property `p` or whose coordinate group
is a proper quotient of its own, then every parametric generalised equation has a parametric cover
by equations with the property `p`. -/
theorem hasParamCover_of_forall (p : ParamGenEq A → Prop)
    (h : ∀ Ω' : ParamGenEq A, Ω'.HasParamCover fun T =>
      p T ∨ T.toGenEq.IsProperQuotient Ω'.toGenEq) (Ω : ParamGenEq A) : Ω.HasParamCover p :=
  (InvImage.wf toGenEq GenEq.wellFounded_isProperQuotient).induction Ω fun Ω ih =>
    (h Ω).bind fun T hT => hT.elim hasParamCover_self (ih T)

/-! ### The equation `y = x` with parameter `x` -/

/-- The generalised equation of `y = x` with `x` as parameter, over `F(a, b)`: an active item
`h₀` (the section of `y`) and a parametric item `h₁` (the section of `x`), with the dual bases
`[0, 1]` on `h₀` and `[1, 2]` on `h₁`, so that its basic equation is `h₀ = h₁`. -/
private abbrev yEqX : ParamGenEq Bool where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := fun μ => by fin_cases μ <;> rfl
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp
  partition := ⟨![.active, .parametric], by decide⟩

/-- One parametric item and no bases: the terminal equation of `y = x`. -/
private abbrev oneParam : ParamGenEq Bool where
  numItems := 1
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right := fun μ => μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive := fun μ => μ.elim0
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp
  partition := ⟨![.parametric], by decide⟩

/-- The equation `y = x` is not terminal: the section of `y` is active. -/
example : ¬ yEqX.IsTerminal := fun h => by
  simpa [yEqX] using yEqX.isTerminal_iff.1 h 0

/-- Labelling the section of `y` as constant does not make `y = x` terminal: the item `h₀` is
neither constant nor free, since it lies in a variable base. -/
example : ¬ (⟨yEqX.toGenEq, ⟨![.constant, .parametric], by decide⟩⟩ : ParamGenEq Bool).IsTerminal :=
  fun h => by
    have := (isTerminal_iff _).1 h 0
    revert this
    decide

-- The equation with one parametric item is terminal.
private theorem isTerminal_oneParam : oneParam.IsTerminal :=
  oneParam.isTerminal_iff.2 fun k => Or.inl (by fin_cases k; rfl)

-- The only parametric item of `y = x` is `h₁`, the section of `x`.
private theorem eq_one_of_isParamItem_yEqX {k : Fin 2} (hk : yEqX.IsParamItem k) : k = 1 := by
  fin_cases k
  · simp [isParamItem_iff] at hk
  · rfl

-- In a solution of `y = x`, the words of `y` and `x` agree.
private theorem word_zero_eq_word_one_yEqX (U : yEqX.Solution) : U.word 0 = U.word 1 := by
  have h := U.subst_eq _ (yEqX.basicEquation_mem_equations 0)
  have h₀ : yEqX.segment 0 1 true = [(Sum.inl 0, true)] := yEqX.segment_succ 0 true
  have h₁ : yEqX.segment 1 2 true = [(Sum.inl 1, true)] := yEqX.segment_succ 1 true
  simp only [GenEq.basicEquation_fst, GenEq.basicEquation_snd] at h
  simpa [yEqX, h₀, h₁] using h

-- Sending both `y` and `x` to the parameter item of `oneParam` maps the points of `oneParam`
-- to points of `y = x`.
private theorem mapsTo_yEqX : Set.MapsTo (wordMap (.id _) fun _ => inr (FreeGroup.of 0))
    (V (.id (FreeGroup Bool)) oneParam.toSystem) (V (.id _) yEqX.toSystem) := fun v _ => by
  have h₀ : yEqX.segment 0 1 true = [(Sum.inl 0, true)] := yEqX.segment_succ 0 true
  have h₁ : yEqX.segment 1 2 true = [(Sum.inl 1, true)] := yEqX.segment_succ 1 true
  refine (GenEq.mem_V_toSystem_iff _).2 <| (GenEq.forall_mem_equations _).2
    ⟨fun μ => ?_, fun _ hb => absurd hb (Finset.notMem_empty _),
      fun _ hc => absurd hc (Finset.notMem_empty _)⟩
  fin_cases μ <;> simp [h₀, h₁]

-- For `y = x`, the terminal equation with one parametric item covers the solutions: the
-- parameter section is retained and `y` is reconstructed as `x`.
private theorem isParamCover_yEqX :
    yEqX.IsParamCover (n := 1) (fun _ => oneParam) (fun _ => ![0, 0, 1]) := by
  have hseg : oneParam.segment 0 1 true = [(Sum.inl 0, true)] := oneParam.segment_succ 0 true
  refine ⟨fun _ k hk => ?_, fun _ _ _ k' _ _ => ?_, fun _ k' _ => ?_, fun U => ?_⟩
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    decide
  · fin_cases k'
    exact oneParam.isParamItem_iff.2 rfl
  · fin_cases k'
    exact ⟨1, yEqX.isParamItem_iff.2 rfl, by decide, by decide⟩
  refine ⟨0, CoordGroup.homOfMapsToWordMap _ _ _ _ mapsTo_yEqX,
    .ofNumBasesEqZero rfl rfl (fun _ => U.word 1) (fun _ => U.isReduced_word 1)
      (fun _ => U.word_ne_nil 1), CoordGroup.gHom_ext fun x => ?_, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [GHom.coe_comp, Function.comp_apply, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of,
      GenEq.Solution.toHom_inr_of, GenEq.Solution.toHom_inr_of]
    fin_cases x
    · simp [word_zero_eq_word_one_yEqX U]
    · simp
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    -- The boundary map sends the boundaries `1` and `2` of `h₁` to `0` and `1`.
    change _ = oneParam.wordElem (oneParam.segment 0 1 true)
    rw [hseg, GenEq.wordElem_singleton_inl, GenEq.item, GenEq.item,
      CoordGroup.genericPoint_apply, CoordGroup.genericPoint_apply,
      CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    simp [hseg]

/-- The equation `y = x` with parameter `x` has a parametric cover by terminal equations. -/
example : yEqX.HasParamCover IsTerminal :=
  hasParamCover_iff.2 ⟨1, _, _, isParamCover_yEqX, fun _ => isTerminal_oneParam⟩

end ParamGenEq

end TauCeti
