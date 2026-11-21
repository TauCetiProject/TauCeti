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

We record what this construction gives for solutions. A *branch* from `Ω` to `T`
(`TauCeti.ParamGenEq.Branch`) is a finite sequence of parametric generalised equations from `Ω` to
`T` with an `F(A)`-homomorphism `πᵢ` of coordinate groups for each step. Its *composites*
(`TauCeti.ParamGenEq.Branch.homs`) are the homomorphisms `σₙ ∘ πₙ ∘ ⋯ ∘ σ₁ ∘ π₁ ∘ σ₀`, where each
`σᵢ` is an automorphism of the coordinate group of the `i`-th equation of the branch fixing the
coefficients and the items outside its active sections (`TauCeti.ParamGenEq.activeAut`), as the
canonical automorphisms of the source do. A *parametric cover* of `Ω`
(`TauCeti.ParamGenEq.IsParamCover`) is a finite family of parametric generalised equations `T j`,
each with a branch `B j` from `Ω` to `T j` and a map `bd j` from the boundaries of `Ω` to those of
`T j`, such that every parametric item `k` of `Ω` is sent to the segment between `bd j k` and
`bd j (k + 1)`, which is nonempty and consists of parametric items, every parametric item of `T j`
lying in the segment of exactly one parametric item of `Ω`; every composite along `B j` sends each
parametric item of `Ω` to its segment; and every solution `U` of `Ω` is `U' ∘ Φ` for a solution
`U'` of some `T j` and a composite `Φ` along `B j`, the segment of each parametric item, evaluated
at `U'`, being the word of `U` at that item letter by letter. The branches are data of the cover
and only the automorphisms `σᵢ` depend on the solution, as in the fundamental sequences of the
source; the values of the parameters are fixed words in the items of `T j`, whatever the `σᵢ`
(Theorem 5 (3)). Conversely, a composite along `B j` is an `F(A)`-homomorphism of coordinate
groups, so composing with it turns every solution of the group equation of `T j` into a solution
of the group equation of `Ω`, with the same values of the parameters (Theorem 5 (2)).

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

* `TauCeti.ParamGenEq.Branch`: a finite sequence of equations with homomorphisms of coordinate
  groups between consecutive ones.
* `TauCeti.ParamGenEq.Branch.homs`: the composites along a branch with automorphisms of the active
  parts.
* `TauCeti.ParamGenEq.IsParamCover`: a finite family of equations with branches covering the
  solutions of `Ω`, with the parametric items sent to segments of parametric items.
* `TauCeti.ParamGenEq.HasParamCover`: `Ω` has a parametric cover by equations with a property.

## Main results

* `TauCeti.ParamGenEq.Branch.comp_mem_homs_append`: composites along two branches compose to a
  composite along their concatenation.
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

/-! ### Branches -/

/-- A branch from `Ω` to `T`: a finite sequence of parametric generalised equations from `Ω` to
`T`, as along a path of a solution tree, with an `F(A)`-homomorphism of coordinate groups for each
step. -/
inductive Branch : ParamGenEq A → ParamGenEq A → Type _
  /-- The branch with no step. -/
  | nil (Ω : ParamGenEq A) : Branch Ω Ω
  /-- A step `π` from `Ω` to `V`, followed by a branch from `V` to `T`. -/
  | cons {Ω V T : ParamGenEq A} (π : GenEq.CoordHom Ω.toGenEq V.toGenEq) (b : Branch V T) :
      Branch Ω T

namespace Branch

/-- The composites along a branch: the homomorphisms `σₙ ∘ πₙ ∘ ⋯ ∘ σ₁ ∘ π₁ ∘ σ₀` of coordinate
groups, where the `πᵢ` are the homomorphisms of the steps and `σᵢ` is an automorphism of the
coordinate group of the `i`-th equation of the branch fixing the coefficients and the items
outside its active sections. -/
def homs : ∀ {Ω T : ParamGenEq A}, Branch Ω T → Set (GenEq.CoordHom Ω.toGenEq T.toGenEq)
  | _, _, nil Ω => {Φ | ∃ σ ∈ Ω.activeAut, ∀ x, Φ x = σ x}
  | Ω, _, cons π b => {Φ | ∃ σ ∈ Ω.activeAut, ∃ Ψ ∈ b.homs, ∀ x, Φ x = Ψ (π (σ x))}

/-- The concatenation of a branch from `Ω` to `V` and a branch from `V` to `T`. -/
def append : ∀ {Ω V T : ParamGenEq A}, Branch Ω V → Branch V T → Branch Ω T
  | _, _, _, nil _, b' => b'
  | _, _, _, cons π b, b' => cons π (b.append b')

variable {Ω V T : ParamGenEq A}

@[simp]
theorem nil_append (b : Branch Ω T) : (nil Ω).append b = b := (rfl)

@[simp]
theorem cons_append (π : GenEq.CoordHom Ω.toGenEq V.toGenEq) {W : ParamGenEq A} (b : Branch V W)
    (b' : Branch W T) : (cons π b).append b' = cons π (b.append b') := (rfl)

theorem mem_homs_nil_iff {Φ : GenEq.CoordHom Ω.toGenEq Ω.toGenEq} :
    Φ ∈ (nil Ω).homs ↔ ∃ σ ∈ Ω.activeAut, ∀ x, Φ x = σ x :=
  Iff.rfl

theorem mem_homs_cons_iff {π : GenEq.CoordHom Ω.toGenEq V.toGenEq} {b : Branch V T}
    {Φ : GenEq.CoordHom Ω.toGenEq T.toGenEq} :
    Φ ∈ (cons π b).homs ↔ ∃ σ ∈ Ω.activeAut, ∃ Ψ ∈ b.homs, ∀ x, Φ x = Ψ (π (σ x)) :=
  Iff.rfl

/-- The identity is a composite along the branch with no step. -/
theorem id_mem_homs_nil (Ω : ParamGenEq A) : GHom.id _ ∈ (nil Ω).homs :=
  ⟨1, one_mem _, fun _ => by simp⟩

/-- The homomorphism of a branch with one step is a composite along it. -/
theorem mem_homs_cons_nil (π : GenEq.CoordHom Ω.toGenEq V.toGenEq) : π ∈ (cons π (nil V)).homs :=
  ⟨1, one_mem _, GHom.id _, id_mem_homs_nil V, fun _ => by simp⟩

-- A composite along a branch, preceded by an automorphism of the coordinate group of its first
-- equation fixing the coefficients and the items outside the active sections, is a composite
-- along the branch.
private theorem comp_mem_homs {b : Branch Ω T} {Ψ : GenEq.CoordHom Ω.toGenEq T.toGenEq}
    (hΨ : Ψ ∈ b.homs) {Φ : GenEq.CoordHom Ω.toGenEq Ω.toGenEq} {σ : MulAut Ω.coordGroup}
    (hσ : σ ∈ Ω.activeAut) (hΦ : ∀ x, Φ x = σ x) : Ψ.comp Φ ∈ b.homs := by
  cases b with
  | nil =>
    obtain ⟨τ, hτ, h⟩ := hΨ
    exact ⟨τ * σ, mul_mem hτ hσ, fun x => by simp [h, hΦ]⟩
  | cons π b =>
    obtain ⟨τ, hτ, Ψ', hΨ', h⟩ := hΨ
    exact ⟨τ * σ, mul_mem hτ hσ, Ψ', hΨ', fun x => by simp [h, hΦ]⟩

-- A composite along the concatenation of two branches is the composite of composites along them.
private theorem exists_of_mem_homs_append {b₁ : Branch Ω V} {b₂ : Branch V T}
    {Φ : GenEq.CoordHom Ω.toGenEq T.toGenEq} (hΦ : Φ ∈ (b₁.append b₂).homs) :
    ∃ Φ₁ ∈ b₁.homs, ∃ Φ₂ ∈ b₂.homs, ∀ x, Φ x = Φ₂ (Φ₁ x) := by
  induction b₁ with
  | nil => exact ⟨GHom.id _, id_mem_homs_nil _, Φ, hΦ, fun _ => by simp⟩
  | cons π b ih =>
    obtain ⟨σ, hσ, Ψ, hΨ, h⟩ := hΦ
    obtain ⟨Φ₁, hΦ₁, Φ₂, hΦ₂, h'⟩ := ih hΨ
    exact ⟨Φ₁.comp (π.comp (GHom.ofMulEquiv σ (mem_activeAut_iff.1 hσ).1)),
      ⟨σ, hσ, Φ₁, hΦ₁, fun _ => by simp⟩, Φ₂, hΦ₂, fun x => by simp [h, h']⟩

/-- Composites along two branches compose to a composite along their concatenation. -/
theorem comp_mem_homs_append {b₁ : Branch Ω V} {b₂ : Branch V T}
    {Φ : GenEq.CoordHom Ω.toGenEq V.toGenEq} {Ψ : GenEq.CoordHom V.toGenEq T.toGenEq}
    (hΦ : Φ ∈ b₁.homs) (hΨ : Ψ ∈ b₂.homs) : Ψ.comp Φ ∈ (b₁.append b₂).homs := by
  induction b₁ with
  | nil =>
    obtain ⟨σ, hσ, h⟩ := hΦ
    exact comp_mem_homs hΨ hσ h
  | cons π b ih =>
    obtain ⟨σ, hσ, Φ', hΦ', h⟩ := hΦ
    exact ⟨σ, hσ, Ψ.comp Φ', ih hΦ' hΨ, fun x => by simp [h]⟩

/-- The composites along the concatenation of two branches are the composites of composites along
the two branches. -/
theorem mem_homs_append_iff {b₁ : Branch Ω V} {b₂ : Branch V T}
    {Φ : GenEq.CoordHom Ω.toGenEq T.toGenEq} :
    Φ ∈ (b₁.append b₂).homs ↔ ∃ Φ₁ ∈ b₁.homs, ∃ Φ₂ ∈ b₂.homs, ∀ x, Φ x = Φ₂ (Φ₁ x) :=
  ⟨exists_of_mem_homs_append, fun ⟨Φ₁, h₁, Φ₂, h₂, h⟩ => by
    rw [show Φ = Φ₂.comp Φ₁ from GHom.ext fun x => by simp [h]]
    exact comp_mem_homs_append h₁ h₂⟩

end Branch

/-! ### Parametric covers -/

/-- The equations `T j`, with the branches `B j` from `Ω` to `T j` and the maps `bd j` on
boundaries, form a parametric cover of `Ω`: each parametric item `k` of `Ω` goes to the nonempty
segment of `T j` between `bd j k` and `bd j (k + 1)`, all of whose items are parametric, every
parametric item of `T j` lying in the segment of exactly one parametric item of `Ω`; every
composite along the branch `B j` sends each parametric item of `Ω` to its segment; and every
solution `U` of `Ω` is the composite of a solution `U'` of some `T j` with a composite along
`B j`, the segment of each parametric item evaluated at `U'` being the word of `U` at that item
letter by letter. -/
structure IsParamCover (Ω : ParamGenEq A) {n : ℕ} (T : Fin n → ParamGenEq A)
    (B : ∀ j, Branch Ω (T j)) (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)) :
    Prop where
  /-- The segment of a parametric item is nonempty. -/
  lt : ∀ j k, Ω.IsParamItem k → bd j k.castSucc < bd j k.succ
  /-- The segment of a parametric item consists of parametric items. -/
  isParamItem : ∀ j k, Ω.IsParamItem k → ∀ k' : Fin (T j).numItems,
    bd j k.castSucc ≤ k'.castSucc → k'.succ ≤ bd j k.succ → (T j).IsParamItem k'
  /-- Every parametric item of a member of the family lies in the segment of exactly one
  parametric item of `Ω`. -/
  existsUnique_isParamItem : ∀ j (k' : Fin (T j).numItems), (T j).IsParamItem k' →
    ∃! k, Ω.IsParamItem k ∧ bd j k.castSucc ≤ k'.castSucc ∧ k'.succ ≤ bd j k.succ
  /-- Every composite along the branch of a member sends each parametric item to its segment. -/
  map_item : ∀ j, ∀ Φ ∈ (B j).homs, ∀ k, Ω.IsParamItem k →
    Φ (Ω.item k) = (T j).wordElem ((T j).segment (bd j k.castSucc) (bd j k.succ) true)
  /-- Every solution factors through a solution of a member of the family by a composite along
  its branch, the segment of each parametric item spelling the word of the solution there. -/
  exists_factor : ∀ U : Ω.Solution, ∃ (j : Fin n), ∃ Φ ∈ (B j).homs, ∃ U' : (T j).Solution,
      U'.toHom.comp Φ = U.toHom ∧ ∀ k, Ω.IsParamItem k →
        substituteVars U'.word ((T j).segment (bd j k.castSucc) (bd j k.succ) true) = U.word k

/-- `Ω` has a parametric cover by finitely many equations with the property `p`. -/
def HasParamCover (Ω : ParamGenEq A) (p : ParamGenEq A → Prop) : Prop :=
  ∃ (n : ℕ) (T : Fin n → ParamGenEq A) (B : ∀ j, Branch Ω (T j))
    (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)),
    Ω.IsParamCover T B bd ∧ ∀ j, p (T j)

theorem hasParamCover_iff {Ω : ParamGenEq A} {p : ParamGenEq A → Prop} :
    Ω.HasParamCover p ↔ ∃ (n : ℕ) (T : Fin n → ParamGenEq A) (B : ∀ j, Branch Ω (T j))
      (bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)),
      Ω.IsParamCover T B bd ∧ ∀ j, p (T j) :=
  Iff.rfl

/-! ### Covers of an equation by itself, and composition of covers -/

-- Every parametric generalised equation covers itself, each parametric item going to itself.
private theorem isParamCover_self (Ω : ParamGenEq A) :
    Ω.IsParamCover (fun _ : Fin 1 => Ω) (fun _ => .nil Ω) fun _ => id where
  lt _ k _ := k.castSucc_lt_succ
  isParamItem _ k hk k' h₁ h₂ := by
    rwa [le_antisymm (Fin.succ_le_succ_iff.1 h₂) (Fin.castSucc_le_castSucc_iff.1 h₁)]
  existsUnique_isParamItem _ k' hk' := ⟨k', ⟨hk', le_rfl, le_rfl⟩, fun _ ⟨_, h₁, h₂⟩ =>
    le_antisymm (Fin.castSucc_le_castSucc_iff.1 h₁) (Fin.succ_le_succ_iff.1 h₂)⟩
  map_item _ _ := fun ⟨_, hσ, h⟩ k hk => by
    rw [h, apply_item_of_mem_activeAut hσ hk]
    simp
  exists_factor U := ⟨0, GHom.id _, Branch.id_mem_homs_nil Ω, U, GHom.comp_id _, fun k _ => by simp⟩

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
  {B : ∀ j, Branch Ω (T j)} {B' : ∀ t, Branch (T j) (S t)}
  (hT : Ω.IsParamCover T B bd) (hS : (T j).IsParamCover S B' bd') (t : Fin m)
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

-- An item `k''` of `S t` in the segment between `bd' t (bd j k)` and `bd' t (bd j (k + 1))` lies in
-- the segment of `S t` of an item of `T j` in the segment of `k`.
omit hS in
private theorem IsParamCover.exists_mem_segment_comp {k : Fin Ω.numItems} (hk : Ω.IsParamItem k)
    {k'' : Fin (S t).numItems} (h₁ : bd' t (bd j k.castSucc) ≤ k''.castSucc)
    (h₂ : k''.succ ≤ bd' t (bd j k.succ)) : ∃ k' : Fin (T j).numItems,
      bd j k.castSucc ≤ k'.castSucc ∧ k'.succ ≤ bd j k.succ ∧ bd' t k'.castSucc ≤ k''.castSucc ∧
        k''.succ ≤ bd' t k'.succ := by
  -- For every boundary `b` of `T j` after `bd j k` with `k''` to the left of `bd' t b`, the item
  -- `k''` lies in the segment of an item of `T j` between `bd j k` and `b`: induction on `b`.
  suffices ∀ b, bd j k.castSucc ≤ b → k''.succ ≤ bd' t b → ∃ k' : Fin (T j).numItems,
      bd j k.castSucc ≤ k'.castSucc ∧ k'.succ ≤ b ∧ bd' t k'.castSucc ≤ k''.castSucc ∧
        k''.succ ≤ bd' t k'.succ from this _ (hT.lt j k hk).le h₂
  have hlt : ¬ k''.succ ≤ bd' t (bd j k.castSucc) := fun h =>
    (h.trans h₁).not_gt k''.castSucc_lt_succ
  intro b
  induction b using Fin.induction with
  | zero => exact fun hab hb => absurd (le_antisymm hab (Fin.zero_le _) ▸ hb) hlt
  | succ i ih =>
    intro hab hk''
    rcases hab.lt_or_eq with hab | hab
    · rw [← Fin.le_castSucc_iff] at hab
      by_cases hi : k''.succ ≤ bd' t i.castSucc
      · obtain ⟨k', h₃, h₄, h₅⟩ := ih hab hi
        exact ⟨k', h₃, h₄.trans i.castSucc_lt_succ.le, h₅⟩
      · exact ⟨i, hab, le_rfl, Fin.le_castSucc_iff.2 (not_le.1 hi), hk''⟩
    · exact absurd (hab ▸ hk'') hlt

private theorem IsParamCover.isParamItem_comp (k : Fin Ω.numItems) (hk : Ω.IsParamItem k)
    (k'' : Fin (S t).numItems) (h₁ : bd' t (bd j k.castSucc) ≤ k''.castSucc)
    (h₂ : k''.succ ≤ bd' t (bd j k.succ)) : (S t).IsParamItem k'' :=
  have ⟨k', h₃, h₄, h₅, h₆⟩ := hT.exists_mem_segment_comp t hk h₁ h₂
  hS.isParamItem t k' (hT.isParamItem j k hk k' h₃ h₄) k'' h₅ h₆

private theorem IsParamCover.existsUnique_isParamItem_comp (k'' : Fin (S t).numItems)
    (hk'' : (S t).IsParamItem k'') : ∃! k, Ω.IsParamItem k ∧
      bd' t (bd j k.castSucc) ≤ k''.castSucc ∧ k''.succ ≤ bd' t (bd j k.succ) := by
  obtain ⟨k', ⟨hk', h₁, h₂⟩, -⟩ := hS.existsUnique_isParamItem t k'' hk''
  obtain ⟨k, ⟨hk, h₃, h₄⟩, -⟩ := hT.existsUnique_isParamItem j k' hk'
  have hmono := (hT.strictMonoOn_comp hS t hk).monotoneOn
  have hk'le := k'.castSucc_lt_succ.le
  have hab := (hT.lt j k hk).le
  refine ⟨k, ⟨hk, (hmono ⟨le_rfl, hab⟩ ⟨h₃, hk'le.trans h₄⟩ h₃).trans h₁,
    h₂.trans (hmono ⟨h₃.trans hk'le, h₄⟩ ⟨hab, le_rfl⟩ h₄)⟩, fun l ⟨hl, h₅, h₆⟩ => ?_⟩
  -- The item `k''` lies in the segment of an item `l'` of `T j` in the segment of `l`; by
  -- uniqueness `l' = k'`, and then `l = k`.
  obtain ⟨l', h₇, h₈, h₉, h₁₀⟩ := hT.exists_mem_segment_comp t hl h₅ h₆
  obtain rfl := (hS.existsUnique_isParamItem t k'' hk'').unique
    ⟨hT.isParamItem j l hl l' h₇ h₈, h₉, h₁₀⟩ ⟨hk', h₁, h₂⟩
  exact (hT.existsUnique_isParamItem j l' hk').unique ⟨hl, h₇, h₈⟩ ⟨hk, h₃, h₄⟩

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
-- `Fin (∑ j, m j) ≃ Σ j, Fin (m j)`, with the concatenated branches, cover `Ω`.
private theorem IsParamCover.comp {Ω : ParamGenEq A} {n : ℕ} {T : Fin n → ParamGenEq A}
    {B : ∀ j, Branch Ω (T j)} {bd : ∀ j, Fin (Ω.numItems + 1) → Fin ((T j).numItems + 1)}
    (hT : Ω.IsParamCover T B bd) {m : Fin n → ℕ} {S : ∀ j, Fin (m j) → ParamGenEq A}
    {B' : ∀ j t, Branch (T j) (S j t)}
    {bd' : ∀ j t, Fin ((T j).numItems + 1) → Fin ((S j t).numItems + 1)}
    (hS : ∀ j, (T j).IsParamCover (S j) (B' j) (bd' j)) :
    Ω.IsParamCover (fun i => S (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2)
      (fun i => (B (finSigmaFinEquiv.symm i).1).append
        (B' (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2))
      fun i k => bd' (finSigmaFinEquiv.symm i).1 (finSigmaFinEquiv.symm i).2
        (bd (finSigmaFinEquiv.symm i).1 k) where
  lt i := hT.lt_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  isParamItem i := hT.isParamItem_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  existsUnique_isParamItem i :=
    hT.existsUnique_isParamItem_comp (hS (finSigmaFinEquiv.symm i).1) (finSigmaFinEquiv.symm i).2
  map_item i _ hΦ k hk := by
    obtain ⟨Φ, hΦ, Ψ, hΨ, h⟩ := Branch.mem_homs_append_iff.1 hΦ
    rw [h, hT.map_item _ Φ hΦ k hk,
      hT.wordElem_comp (hS _) _ ((hS _).map_item _ Ψ hΨ) hk]
  exists_factor U := by
    obtain ⟨j, Φ, hΦ, U', hU', hw⟩ := hT.exists_factor U
    obtain ⟨t, Ψ, hΨ, U'', hU'', hw'⟩ := (hS j).exists_factor U'
    refine ⟨finSigmaFinEquiv ⟨j, t⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact ⟨Ψ.comp Φ, Branch.comp_mem_homs_append hΦ hΨ, U'', by
      rw [← GHom.comp_assoc, hU'', hU'], fun k hk => by
        rw [hT.substituteVars_comp (hS j) t hw' hk, hw k hk]⟩

/-- A parametric generalised equation with the property `p` has a parametric cover by equations
with the property `p`: itself. -/
theorem hasParamCover_self {Ω : ParamGenEq A} {p : ParamGenEq A → Prop} (hp : p Ω) :
    Ω.HasParamCover p :=
  hasParamCover_iff.2 ⟨1, _, _, _, isParamCover_self Ω, fun _ => hp⟩

/-- Parametric covers compose: if `Ω` has a parametric cover by equations with the property `q`,
and every equation with the property `q` has a parametric cover by equations with the property
`p`, then `Ω` has a parametric cover by equations with the property `p`. -/
theorem HasParamCover.bind {Ω : ParamGenEq A} {p q : ParamGenEq A → Prop} (h : Ω.HasParamCover q)
    (hq : ∀ T, q T → T.HasParamCover p) : Ω.HasParamCover p := by
  obtain ⟨n, T, B, bd, hT, hqT⟩ := hasParamCover_iff.1 h
  choose m S B' bd' hS hpS using fun j => hq (T j) (hqT j)
  exact hasParamCover_iff.2 ⟨_, _, _, _, hT.comp hS, fun i => hpS _ _⟩

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
private theorem isParamCover_yEqX : yEqX.IsParamCover (n := 1) (fun _ => oneParam)
    (fun _ => .cons (CoordGroup.homOfMapsToWordMap _ _ _ _ mapsTo_yEqX) (.nil oneParam))
    (fun _ => ![0, 0, 1]) := by
  have hseg : oneParam.segment 0 1 true = [(Sum.inl 0, true)] := oneParam.segment_succ 0 true
  have hπ : CoordGroup.homOfMapsToWordMap _ _ _ _ mapsTo_yEqX (yEqX.item 1) = oneParam.item 0 := by
    rw [GenEq.item, GenEq.item, CoordGroup.genericPoint_apply, CoordGroup.genericPoint_apply,
      CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]
  refine ⟨fun _ k hk => ?_, fun _ _ _ k' _ _ => ?_, fun _ k' _ => ?_,
    fun _ _ ⟨σ, hσ, _, ⟨τ, hτ, hΨ⟩, h⟩ k hk => ?_, fun U => ?_⟩
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    decide
  · fin_cases k'
    exact oneParam.isParamItem_iff.2 rfl
  · fin_cases k'
    exact ⟨1, ⟨yEqX.isParamItem_iff.2 rfl, by decide, by decide⟩,
      fun k hk => eq_one_of_isParamItem_yEqX hk.1⟩
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    -- The boundary map sends the boundaries `1` and `2` of `h₁` to `0` and `1`.
    change _ = oneParam.wordElem (oneParam.segment 0 1 true)
    rw [h, apply_item_of_mem_activeAut hσ hk, hΨ, hπ,
      apply_item_of_mem_activeAut hτ (oneParam.isParamItem_iff.2 rfl), hseg,
      GenEq.wordElem_singleton_inl]
  refine ⟨0, _, Branch.mem_homs_cons_nil _,
    .ofNumBasesEqZero rfl rfl (fun _ => U.word 1) (fun _ => U.isReduced_word 1)
      (fun _ => U.word_ne_nil 1), CoordGroup.gHom_ext fun x => ?_, fun k hk => ?_⟩
  · rw [GHom.coe_comp, Function.comp_apply, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of,
      GenEq.Solution.toHom_inr_of, GenEq.Solution.toHom_inr_of]
    fin_cases x
    · simp [word_zero_eq_word_one_yEqX U]
    · simp
  · obtain rfl := eq_one_of_isParamItem_yEqX hk
    simp [hseg]

/-- The equation `y = x` with parameter `x` has a parametric cover by terminal equations. -/
example : yEqX.HasParamCover IsTerminal :=
  hasParamCover_iff.2 ⟨1, _, _, _, isParamCover_yEqX, fun _ => isTerminal_oneParam⟩

end ParamGenEq

end TauCeti
