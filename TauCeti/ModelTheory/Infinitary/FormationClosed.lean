/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Fragment
public import TauCeti.ModelTheory.Infinitary.Symbols
import Mathlib.ModelTheory.Encoding
import TauCeti.ModelTheory.Basic

/-!
# Formation-closed fragments of `L_{ω₁ω}`

A fragment of `L_{ω₁ω}` is only required to be closed under taking components. A
**formation-closed** fragment is also closed under forming formulas: it contains every atomic
formula and `⊥` at every arity, and it is closed under implication, universal quantification and
relabelling of bound positions (`BoundedFormulaInf.mapBound`, which includes weakening
`BoundedFormulaInf.castLE`). Formation-closed fragments play the role of the fragments of Marker's
*Lectures on Infinitary Model Theory*; they are the fragments over which consistency properties
built from satisfiable theories and the omitting types theorem are set up, since forming the
negation, the existential closure or a relabelling of a member must stay inside the fragment.

Marker's fragments are also closed under a formal negation and under substitution of terms. The
syntax here has no formal negation: `¬φ` is `φ.imp ⊥`, so closure under implication and
containing `⊥` already give closure under negation. Closure under substitution of terms does not
follow from the other conditions (substituting into a countable conjunction of members need not
give a member), and it is not imposed because nothing built on formation-closed fragments here
uses it.

Unlike a fragment, a formation-closed fragment determines the size of the language: every function
and relation symbol occurs in an atomic member. So the formation closure of a countable set is
countable exactly over languages with countably many function and relation symbols.

## Main definitions

* `FirstOrder.Language.Fragment.FormationClosed`: a fragment containing the atomic formulas and
  `⊥` and closed under implication, universal quantification and relabelling.
* `FirstOrder.Language.Fragment.formationClosure`: the least formation-closed fragment containing
  a set of formulas.

## Main results

* `FirstOrder.Language.Fragment.FormationClosed.not_mem_iff`,
  `FirstOrder.Language.Fragment.FormationClosed.ex_mem`,
  `FirstOrder.Language.Fragment.FormationClosed.alls_mem` and their companions: the derived
  connectives and quantifier closures of members are members.
* `FirstOrder.Language.Fragment.formationClosure_le_iff`: leastness of the formation closure.
* `FirstOrder.Language.Fragment.formationClosure_countable`: over a language with countably many
  function and relation symbols, a countable set has a countable formation closure.
* `FirstOrder.Language.Fragment.FormationClosed.countable_functions` and
  `FirstOrder.Language.Fragment.FormationClosed.countable_relations`: conversely, a countable
  formation-closed fragment forces countably many function and relation symbols.
* `FirstOrder.Language.BoundedFormulaInf.countable_setOf_isAtomic`: over a countable language and
  countably many free variables, there are countably many atomic formulas of each arity.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1.
-/

public section

universe u v u' uι

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace BoundedFormulaInf

/-- Over a language with countably many function and relation symbols and a countable type of
free variables, there are countably many atomic formulas with `n` bound positions. -/
theorem countable_setOf_isAtomic {ι : Type uι} {α : Type u'} {n : ℕ} [Countable α]
    [Countable (Σ l, L.Functions l)] [Countable (Σ l, L.Relations l)] :
    {φ : L.BoundedFormulaInf ι α n | φ.IsAtomic}.Countable := by
  have h : {φ : L.BoundedFormulaInf ι α n | φ.IsAtomic} ⊆
      Set.range (fun t : L.Term (α ⊕ Fin n) × L.Term (α ⊕ Fin n) => equal t.1 t.2) ∪
        Set.range fun x : Σ l, L.Relations l × (Fin l → L.Term (α ⊕ Fin n)) =>
          (rel x.2.1 x.2.2 : L.BoundedFormulaInf ι α n) := by
    rintro _ (⟨t₁, t₂⟩ | ⟨R, ts⟩)
    · exact Or.inl ⟨(t₁, t₂), rfl⟩
    · exact Or.inr ⟨⟨_, R, ts⟩, rfl⟩
  exact ((Set.countable_range _).union (Set.countable_range _)).mono h

end BoundedFormulaInf

namespace Fragment

open BoundedFormulaInf

/-- A fragment is **formation-closed** when it contains every atomic formula and `⊥` at every
arity, and is closed under implication, universal quantification and relabelling of bound
positions. -/
structure FormationClosed (A : Fragment L) : Prop where
  /-- `⊥` is a member at every arity. -/
  bot_mem (n : ℕ) : (⟨n, ⊥⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A
  /-- Every atomic formula is a member. -/
  atomic_mem {n : ℕ} {φ : L.BoundedFormulaω Empty n} (h : φ.IsAtomic) :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A
  /-- The implication between two members is a member. -/
  imp_mem {n : ℕ} {φ ψ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A → (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
      (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A
  /-- The universal quantification of a member over its last bound position is a member. -/
  all_mem {n : ℕ} {φ : L.BoundedFormulaω Empty (n + 1)} :
    (⟨n + 1, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
      (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A
  /-- Relabelling the bound positions of a member gives a member. -/
  mapBound_mem {m k : ℕ} {φ : L.BoundedFormulaω Empty m} (f : Fin m → Fin k) :
    (⟨m, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A →
      (⟨k, φ.mapBound f⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A

namespace FormationClosed

variable {A : Fragment L} (hA : A.FormationClosed) {n : ℕ}
include hA

/-- An implication belongs to a formation-closed fragment exactly when both sides do. -/
@[simp]
theorem imp_mem_iff {φ ψ : L.BoundedFormulaω Empty n} :
    (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
        (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  ⟨fun h => ⟨A.imp_left_mem h, A.imp_right_mem h⟩, fun h => hA.imp_mem h.1 h.2⟩

/-- A universal quantification belongs to a formation-closed fragment exactly when its body
does. -/
@[simp]
theorem all_mem_iff {φ : L.BoundedFormulaω Empty (n + 1)} :
    (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n + 1, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  ⟨A.all_mem, hA.all_mem⟩

/-- A negation belongs to a formation-closed fragment exactly when the negated formula does. -/
@[simp]
theorem not_mem_iff {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ.not⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.imp_mem_iff.trans (and_iff_left (hA.bot_mem n))

/-- `⊤` is a member of a formation-closed fragment at every arity. -/
@[simp]
theorem top_mem (n : ℕ) : (⟨n, ⊤⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  rw [top_def]
  exact hA.not_mem_iff.2 (hA.bot_mem n)

/-- A conjunction belongs to a formation-closed fragment exactly when both conjuncts do. -/
@[simp]
theorem inf_mem_iff {φ ψ : L.BoundedFormulaω Empty n} :
    (⟨n, φ ⊓ ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
        (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  rw [inf_def, hA.not_mem_iff, hA.imp_mem_iff, hA.not_mem_iff]

/-- The conjunction of two members of a formation-closed fragment is a member. -/
theorem inf_mem {φ ψ : L.BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (hψ : (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, φ ⊓ ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.inf_mem_iff.2 ⟨hφ, hψ⟩

/-- A disjunction belongs to a formation-closed fragment exactly when both disjuncts do. -/
@[simp]
theorem sup_mem_iff {φ ψ : L.BoundedFormulaω Empty n} :
    (⟨n, φ ⊔ ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
        (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  rw [sup_def, hA.imp_mem_iff, hA.not_mem_iff]

/-- The disjunction of two members of a formation-closed fragment is a member. -/
theorem sup_mem {φ ψ : L.BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (hψ : (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, φ ⊔ ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.sup_mem_iff.2 ⟨hφ, hψ⟩

/-- A biconditional belongs to a formation-closed fragment exactly when both sides do. -/
@[simp]
theorem iff_mem_iff {φ ψ : L.BoundedFormulaω Empty n} :
    (⟨n, φ.iff ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
        (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  rw [BoundedFormulaInf.iff_def, hA.inf_mem_iff, hA.imp_mem_iff, hA.imp_mem_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, h.2, h.1⟩⟩

/-- The biconditional of two members of a formation-closed fragment is a member. -/
theorem iff_mem {φ ψ : L.BoundedFormulaω Empty n}
    (hφ : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A)
    (hψ : (⟨n, ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, φ.iff ψ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.iff_mem_iff.2 ⟨hφ, hψ⟩

/-- An existential quantification belongs to a formation-closed fragment exactly when its body
does. -/
@[simp]
theorem ex_mem_iff {φ : L.BoundedFormulaω Empty (n + 1)} :
    (⟨n, φ.ex⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ↔
      (⟨n + 1, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.not_mem_iff.trans (hA.all_mem_iff.trans hA.not_mem_iff)

/-- The existential quantification of a member of a formation-closed fragment is a member. -/
theorem ex_mem {φ : L.BoundedFormulaω Empty (n + 1)}
    (h : (⟨n + 1, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, φ.ex⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A :=
  hA.ex_mem_iff.2 h

/-- The universal closure of a member of a formation-closed fragment is a member. -/
theorem alls_mem {φ : L.BoundedFormulaω Empty n}
    (h : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨0, φ.alls⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  induction n with
  | zero => rwa [alls_zero]
  | succ n ih => rw [alls_succ]; exact ih (hA.all_mem h)

/-- The existential closure of a member of a formation-closed fragment is a member. -/
theorem exs_mem {φ : L.BoundedFormulaω Empty n}
    (h : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨0, φ.exs⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  induction n with
  | zero => rwa [exs_zero]
  | succ n ih => rw [exs_succ]; exact ih (hA.ex_mem h)

/-- Weakening a member of a formation-closed fragment to more bound positions gives a member. -/
theorem castLE_mem {m : ℕ} {φ : L.BoundedFormulaω Empty m} (hmn : m ≤ n)
    (h : (⟨m, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A) :
    (⟨n, castLE hmn φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  rw [castLE_def]
  exact hA.mapBound_mem _ h

/-- A countable formation-closed fragment forces countably many function symbols: each occurs in
an atomic member. -/
theorem countable_functions (hc : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) :
    Countable (Σ l, L.Functions l) := by
  have h : (Set.univ : Set (Σ l, L.Functions l)) ⊆
      ⋃ p ∈ (A : Set (Σ n, L.BoundedFormulaω Empty n)), p.2.functionsIn := by
    rintro ⟨l, f⟩ -
    let t : L.Term (Empty ⊕ Fin l) := .func f fun i => .var (.inr i)
    refine Set.mem_iUnion₂.2 ⟨⟨l, equal t t⟩, hA.atomic_mem (.equal t t), ?_⟩
    simp [t, Term.functionsIn_func]
  exact Set.countable_univ_iff.1 ((hc.biUnion fun p _ => p.2.functionsIn_countable).mono h)

/-- A countable formation-closed fragment forces countably many relation symbols: each occurs in
an atomic member. -/
theorem countable_relations (hc : (A : Set (Σ n, L.BoundedFormulaω Empty n)).Countable) :
    Countable (Σ l, L.Relations l) := by
  have h : (Set.univ : Set (Σ l, L.Relations l)) ⊆
      ⋃ p ∈ (A : Set (Σ n, L.BoundedFormulaω Empty n)), p.2.relationsIn := by
    rintro ⟨l, R⟩ -
    refine Set.mem_iUnion₂.2
      ⟨⟨l, rel R fun i => .var (.inr i)⟩, hA.atomic_mem (.rel R _), ?_⟩
    simp
  exact Set.countable_univ_iff.1 ((hc.biUnion fun p _ => p.2.relationsIn_countable).mono h)

end FormationClosed

/-- The top fragment, of all formulas, is formation-closed. -/
theorem formationClosed_top : (⊤ : Fragment L).FormationClosed where
  bot_mem _ := mem_top _
  atomic_mem _ := mem_top _
  imp_mem _ _ := mem_top _
  all_mem _ := mem_top _
  mapBound_mem _ _ := mem_top _

/-- An intersection of formation-closed fragments is formation-closed. -/
theorem FormationClosed.sInf {𝒜 : Set (Fragment L)} (h : ∀ A ∈ 𝒜, A.FormationClosed) :
    (sInf 𝒜).FormationClosed where
  bot_mem n := mem_sInf.2 fun A hA => (h A hA).bot_mem n
  atomic_mem hφ := mem_sInf.2 fun A hA => (h A hA).atomic_mem hφ
  imp_mem hφ hψ := mem_sInf.2 fun A hA => (h A hA).imp_mem (mem_sInf.1 hφ A hA) (mem_sInf.1 hψ A hA)
  all_mem hφ := mem_sInf.2 fun A hA => (h A hA).all_mem (mem_sInf.1 hφ A hA)
  mapBound_mem f hφ := mem_sInf.2 fun A hA => (h A hA).mapBound_mem f (mem_sInf.1 hφ A hA)

/-- The intersection of two formation-closed fragments is formation-closed. -/
theorem FormationClosed.inf {A B : Fragment L} (hA : A.FormationClosed) (hB : B.FormationClosed) :
    (A ⊓ B).FormationClosed := by
  rw [← sInf_pair]
  exact FormationClosed.sInf (by simp [hA, hB])

/-! ### The formation closure -/

/-- The **formation closure** of a set of formulas: the least formation-closed fragment containing
it. -/
def formationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  sInf {A | A.FormationClosed ∧ S ⊆ A}

/-- A formula belongs to the formation closure of `S` exactly when it belongs to every
formation-closed fragment containing `S`. -/
theorem mem_formationClosure {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ formationClosure S ↔ ∀ A : Fragment L, A.FormationClosed → S ⊆ A → p ∈ A := by
  simp [formationClosure, and_imp]

/-- The formation closure is formation-closed. -/
theorem formationClosed_formationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (formationClosure S).FormationClosed :=
  FormationClosed.sInf fun _ hA => hA.1

/-- A set of formulas lies in its formation closure. -/
theorem subset_formationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    S ⊆ formationClosure S :=
  fun _ hp => mem_formationClosure.2 fun _ _ hS => hS hp

/-- **Leastness.** The formation closure of `S` lies below a formation-closed fragment exactly
when `S` does. -/
theorem formationClosure_le_iff {S : Set (Σ n, L.BoundedFormulaω Empty n)} {A : Fragment L}
    (hA : A.FormationClosed) : formationClosure S ≤ A ↔ S ⊆ A :=
  ⟨fun h => (subset_formationClosure S).trans (SetLike.coe_subset_coe.2 h),
    fun h => sInf_le ⟨hA, h⟩⟩

/-- The formation closure is monotone. -/
theorem formationClosure_mono {S T : Set (Σ n, L.BoundedFormulaω Empty n)} (h : S ⊆ T) :
    formationClosure S ≤ formationClosure (L := L) T :=
  (formationClosure_le_iff (formationClosed_formationClosure T)).2
    (h.trans (subset_formationClosure T))

/-- The fragment generated by `S` lies below its formation closure. -/
theorem generated_le_formationClosure (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    generated S ≤ formationClosure S :=
  generated_le_iff.2 (subset_formationClosure S)

/-- A formation-closed fragment is its own formation closure. -/
theorem FormationClosed.formationClosure_eq {A : Fragment L} (hA : A.FormationClosed) :
    formationClosure (A : Set (Σ n, L.BoundedFormulaω Empty n)) = A :=
  le_antisymm ((formationClosure_le_iff hA).2 subset_rfl) (subset_formationClosure _)

/-! ### Countability of the formation closure

The formation closure of a countable set is the union of countably many countable stages: start
from the set, the atomic formulas and `⊥` at every arity, and at each stage add the implications,
universal quantifications and relabellings of members of the previous stage, closing under
components. -/

/-- The members of a set of tagged formulas at arity `n`. -/
private def level (X : Set (Σ n, L.BoundedFormulaω Empty n)) (n : ℕ) :
    Set (L.BoundedFormulaω Empty n) :=
  {φ | ⟨n, φ⟩ ∈ X}

private theorem level_countable {X : Set (Σ n, L.BoundedFormulaω Empty n)} (hX : X.Countable)
    (n : ℕ) : (level X n).Countable :=
  hX.preimage sigma_mk_injective

/-- One stage of formation: the implications, universal quantifications and relabellings of
members of `X`, together with `X`, closed under components. -/
private def formationStep (X : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  generated (X ∪
    (⋃ n, Set.image2 (fun φ ψ => (⟨n, φ.imp ψ⟩ : Σ n, L.BoundedFormulaω Empty n))
      (level X n) (level X n)) ∪
    (⋃ n, (fun φ => (⟨n, φ.all⟩ : Σ n, L.BoundedFormulaω Empty n)) '' level X (n + 1)) ∪
    ⋃ m, ⋃ k, ⋃ f : Fin m → Fin k,
      (fun φ => (⟨k, φ.mapBound f⟩ : Σ n, L.BoundedFormulaω Empty n)) '' level X m)

private theorem subset_formationStep (X : Set (Σ n, L.BoundedFormulaω Empty n)) :
    X ⊆ formationStep X :=
  fun _ hp => subset_generated _ (Or.inl (Or.inl (Or.inl hp)))

private theorem formationStep_countable {X : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hX : X.Countable) :
    ((formationStep X : Fragment L) : Set (Σ n, L.BoundedFormulaω Empty n)).Countable :=
  generated_countable (((hX.union (Set.countable_iUnion fun n =>
    (level_countable hX n).image2 (level_countable hX n) _)).union
      (Set.countable_iUnion fun n => (level_countable hX (n + 1)).image _)).union
        (Set.countable_iUnion fun m => Set.countable_iUnion fun _ => Set.countable_iUnion fun _ =>
          (level_countable hX m).image _))

/-- The stages of the formation closure of `S`. -/
private def formationStage (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    ℕ → Set (Σ n, L.BoundedFormulaω Empty n)
  | 0 => S ∪ {p | p.2.IsAtomic} ∪ Set.range fun n => ⟨n, ⊥⟩
  | k + 1 => formationStep (formationStage S k)

private theorem formationStage_mono (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Monotone (formationStage S) :=
  monotone_nat_of_le_succ fun k => subset_formationStep (formationStage S k)

private theorem formationStage_countable [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) (k : ℕ) : (formationStage S k).Countable := by
  induction k with
  | zero =>
    have h : {p : Σ n, L.BoundedFormulaω Empty n | p.2.IsAtomic} ⊆
        ⋃ n, Sigma.mk n '' {φ : L.BoundedFormulaω Empty n | φ.IsAtomic} :=
      fun p hp => Set.mem_iUnion.2 ⟨p.1, p.2, hp, rfl⟩
    exact (hS.union ((Set.countable_iUnion fun _ => countable_setOf_isAtomic.image _).mono h)).union
      (Set.countable_range _)
  | succ k ih => exact formationStep_countable ih

/-- The union of the stages of the formation closure of `S`, as a fragment. -/
private def formationLimit (S : Set (Σ n, L.BoundedFormulaω Empty n)) : Fragment L :=
  ⨆ k, formationStep (formationStage S k)

private theorem mem_formationLimit {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    {p : Σ n, L.BoundedFormulaω Empty n} : p ∈ formationLimit S ↔ ∃ k, p ∈ formationStage S k := by
  rw [formationLimit, _root_.iSup, mem_sSup, Set.exists_range_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k + 1, hk⟩, fun ⟨k, hk⟩ => ⟨k, subset_formationStep _ hk⟩⟩

private theorem formationClosed_formationLimit (S : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (formationLimit S).FormationClosed where
  bot_mem n := mem_formationLimit.2 ⟨0, Or.inr ⟨n, rfl⟩⟩
  atomic_mem h := mem_formationLimit.2 ⟨0, Or.inl (Or.inr h)⟩
  imp_mem hφ hψ := by
    obtain ⟨i, hi⟩ := mem_formationLimit.1 hφ
    obtain ⟨j, hj⟩ := mem_formationLimit.1 hψ
    refine mem_formationLimit.2 ⟨max i j + 1, subset_generated _ (Or.inl (Or.inl (Or.inr ?_)))⟩
    exact Set.mem_iUnion.2 ⟨_, Set.mem_image2_of_mem
      (formationStage_mono S (le_max_left i j) hi) (formationStage_mono S (le_max_right i j) hj)⟩
  all_mem hφ := by
    obtain ⟨i, hi⟩ := mem_formationLimit.1 hφ
    exact mem_formationLimit.2 ⟨i + 1, subset_generated _
      (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨_, Set.mem_image_of_mem _ hi⟩)))⟩
  mapBound_mem f hφ := by
    obtain ⟨i, hi⟩ := mem_formationLimit.1 hφ
    exact mem_formationLimit.2 ⟨i + 1, subset_generated _ (Or.inr (Set.mem_iUnion.2 ⟨_,
      Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨f, Set.mem_image_of_mem _ hi⟩⟩⟩))⟩

/-- **Countability.** Over a language with countably many function and relation symbols, the
formation closure of a countable set of formulas is countable. -/
theorem formationClosure_countable [Countable (Σ l, L.Functions l)]
    [Countable (Σ l, L.Relations l)] {S : Set (Σ n, L.BoundedFormulaω Empty n)}
    (hS : S.Countable) :
    ((formationClosure S : Fragment L) : Set (Σ n, L.BoundedFormulaω Empty n)).Countable := by
  refine ((Set.countable_iUnion (formationStage_countable hS)).mono
    fun p hp => Set.mem_iUnion.2 (mem_formationLimit.1 hp)).mono
    (SetLike.coe_subset_coe.2 ((formationClosure_le_iff (formationClosed_formationLimit S)).2 ?_))
  exact fun p hp => mem_formationLimit.2 ⟨0, Or.inl (Or.inl hp)⟩

end Fragment

end Language

end FirstOrder
