/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Prod
public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic

/-!
# Surgery on generalised equations: removing variable bases

The elementary transformations of Makanin's process (Kharlampovich–Myasnikov, §5.1) delete and
insert bases and boundaries of a generalised equation. The bases of a `TauCeti.GenEq` are indexed
by `Fin`, so deleting bases renumbers the remaining ones. This file deletes a set `S` of variable
bases closed under duality together with every boundary connection through a base of `S`
(`TauCeti.GenEq.removeBases`); the remaining bases keep their order. The special case of a pair of
dual bases `μ, Δ(μ)` (`TauCeti.GenEq.removePair`) is the deletion of bases performed by the
removal of a pair of matched bases (ET3) and of a lonely base (ET4).

The items and the constant bases, hence the variables `h₁, …, h_ρ` of the equations, are
unchanged. Every equation of the result is an equation of `Ω`, and every other equation of `Ω` is
the basic equation of a base of `S` or the boundary equation of a connection through one.
Consequently:

* every solution of `Ω` is a solution of the result, with the same words
  (`TauCeti.GenEq.Solution.removeBases`);
* every group solution of `Ω*` is a group solution of the result, and conversely when every
  removed equation has two identical sides (`TauCeti.GenEq.V_toSystem_removeBases_subset`); the
  identity on the items then induces an isomorphism of coordinate groups
  (`TauCeti.GroupAlgGeom.CoordGroup.homOfVSubset`);
* removing bases preserves formal consistency
  (`TauCeti.GenEq.IsFormallyConsistent.removeBases`);
* if no boundary connection passes through `μ`, the system `Ω*` and the system of the result
  together with the basic equation of `μ` present the same group
  (`TauCeti.GenEq.normalClosure_toSystem_eq_insert_removePair`).

## Main definitions

* `TauCeti.GenEq.removeBases`: remove a set of variable bases closed under duality, with the
  boundary connections through them.
* `TauCeti.GenEq.removePair`: remove a pair of dual bases `μ, Δ(μ)`.
* `TauCeti.GenEq.Solution.removeBases`, `TauCeti.GenEq.Solution.removePair`: a solution of `Ω` as
  a solution of the result.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1 (ET3 and ET4).
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom

variable {A : Type*} (Ω : GenEq A)

/-! ### Removing a set of variable bases -/

variable {Ω} in
/-- The dual of a base outside a set of bases closed under duality lies outside that set. -/
theorem dual_notMem {S : Finset (Fin Ω.numBases)} (hS : ∀ μ ∈ S, Ω.dual μ ∈ S) {μ : Fin Ω.numBases}
    (hμ : μ ∉ S) : Ω.dual μ ∉ S :=
  fun h => hμ (Ω.dual_involutive μ ▸ hS _ h)

/-- The duality of the bases outside a set `S` of bases closed under duality, with these bases
numbered in increasing order by `Sᶜ.orderEmbOfFin rfl`. -/
def dualCompl (S : Finset (Fin Ω.numBases)) (hS : ∀ μ ∈ S, Ω.dual μ ∈ S) (ν : Fin Sᶜ.card) :
    Fin Sᶜ.card :=
  (Sᶜ.orderIsoOfFin rfl).symm ⟨Ω.dual (Sᶜ.orderEmbOfFin rfl ν),
    Finset.mem_compl.2 (dual_notMem hS (Finset.mem_compl.1 (Sᶜ.orderEmbOfFin_mem rfl ν)))⟩

variable {Ω} {S : Finset (Fin Ω.numBases)} (hS : ∀ μ ∈ S, Ω.dual μ ∈ S)

/-- The renumbered duality is the duality of `Ω`. -/
@[simp]
theorem orderEmbOfFin_dualCompl (ν : Fin Sᶜ.card) :
    Sᶜ.orderEmbOfFin rfl (Ω.dualCompl S hS ν) = Ω.dual (Sᶜ.orderEmbOfFin rfl ν) :=
  congrArg Subtype.val ((Sᶜ.orderIsoOfFin rfl).apply_symm_apply _)

/-- The renumbered duality is an involution. -/
theorem dualCompl_involutive : Function.Involutive (Ω.dualCompl S hS) := fun ν =>
  (Sᶜ.orderEmbOfFin rfl).injective <| by simp [Ω.dual_involutive _]

-- Reducible, so that the items of the result are reducibly those of `Ω`: the statements comparing
-- the equations, systems and solutions of `Ω` and of the result live over `Fin Ω.numItems`.
variable (Ω) in
/-- Remove a set `S` of variable bases closed under duality, together with all boundary
connections through bases of `S`. The remaining bases are renumbered in increasing order: the
base `ν` of the result is the base `Sᶜ.orderEmbOfFin rfl ν` of `Ω`. The items and the constant
bases are unchanged. -/
abbrev removeBases (S : Finset (Fin Ω.numBases)) (hS : ∀ μ ∈ S, Ω.dual μ ∈ S) : GenEq A where
  numItems := Ω.numItems
  numBases := Sᶜ.card
  left ν := Ω.left (Sᶜ.orderEmbOfFin rfl ν)
  right ν := Ω.right (Sᶜ.orderEmbOfFin rfl ν)
  left_lt_right ν := Ω.left_lt_right _
  sign ν := Ω.sign (Sᶜ.orderEmbOfFin rfl ν)
  dual := Ω.dualCompl S hS
  dual_involutive := dualCompl_involutive hS
  constBases := Ω.constBases
  connections :=
    Finset.univ.filter fun c => (c.1, Sᶜ.orderEmbOfFin rfl c.2.1, c.2.2) ∈ Ω.connections
  bounds_of_mem_connections c hc := by
    simpa using Ω.bounds_of_mem_connections _ (Finset.mem_filter.1 hc).2
  dual_mem_connections c hc := by
    simpa using Ω.dual_mem_connections _ (Finset.mem_filter.1 hc).2

/-- Removing the bases of `S` leaves `numBases - #S` bases. -/
theorem numBases_removeBases : (Ω.removeBases S hS).numBases = Ω.numBases - S.card := by
  simp [Finset.card_compl]

/-- Removing a nonempty set of bases decreases the number of bases. -/
theorem numBases_removeBases_lt (hne : S.Nonempty) :
    (Ω.removeBases S hS).numBases < Ω.numBases := by
  simpa using (Finset.card_compl_lt_iff_nonempty S).2 hne

/-- The boundary connections of the result are those of `Ω` through the remaining bases. -/
theorem mem_connections_removeBases
    {c : Fin (Ω.numItems + 1) × Fin (Ω.removeBases S hS).numBases × Fin (Ω.numItems + 1)} :
    c ∈ (Ω.removeBases S hS).connections ↔
      (c.1, Sᶜ.orderEmbOfFin rfl c.2.1, c.2.2) ∈ Ω.connections := by
  simp

/-! ### The equations after removing bases -/

/-- The segments `h[i, j] ^ ±1` only depend on the items, which removing bases keeps. -/
@[simp]
theorem segment_removeBases (i j : ℕ) (s : Bool) :
    (Ω.removeBases S hS).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- The basic equation of a remaining base is its basic equation in `Ω`. -/
@[simp]
theorem basicEquation_removeBases (ν : Fin (Ω.removeBases S hS).numBases) :
    (Ω.removeBases S hS).basicEquation ν = Ω.basicEquation (Sᶜ.orderEmbOfFin rfl ν) :=
  Prod.ext (by simp) (by simp)

/-- Removing variable bases keeps the coefficient equations. -/
@[simp]
theorem coeffEquation_removeBases (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.removeBases S hS).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The boundary equation of a remaining connection is its boundary equation in `Ω`. -/
@[simp]
theorem boundaryEquation_removeBases
    (c : Fin (Ω.numItems + 1) × Fin (Ω.removeBases S hS).numBases × Fin (Ω.numItems + 1)) :
    (Ω.removeBases S hS).boundaryEquation c =
      Ω.boundaryEquation (c.1, Sᶜ.orderEmbOfFin rfl c.2.1, c.2.2) := by
  refine Prod.ext (by simp) ?_
  by_cases h : Ω.sign (Sᶜ.orderEmbOfFin rfl c.2.1) =
      Ω.sign (Ω.dual (Sᶜ.orderEmbOfFin rfl c.2.1)) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, h]

/-- The equations of the result are equations of `Ω`. -/
theorem equations_removeBases_subset : (Ω.removeBases S hS).equations ⊆ Ω.equations :=
  ((Ω.removeBases S hS).forall_mem_equations (P := (· ∈ Ω.equations))).2
    ⟨fun ν => basicEquation_removeBases hS ν ▸ Ω.basicEquation_mem_equations _,
      fun b hb => coeffEquation_removeBases hS b ▸ Ω.coeffEquation_mem_equations hb,
      fun c hc => boundaryEquation_removeBases hS c ▸
        Ω.boundaryEquation_mem_equations ((mem_connections_removeBases hS).1 hc)⟩

/-- The equations of `Ω` are those of the result, the basic equations of the bases of `S`, and the
boundary equations of the connections through bases of `S`. -/
theorem equations_subset_union_removeBases :
    Ω.equations ⊆ (Ω.removeBases S hS).equations ∪
      (Ω.basicEquation '' S ∪ Ω.boundaryEquation '' {c | c ∈ Ω.connections ∧ c.2.1 ∈ S}) := by
  refine (Ω.forall_mem_equations (P := (· ∈ _))).2 ⟨fun μ => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · by_cases hμ : μ ∈ S
    · exact Or.inr (Or.inl ⟨μ, hμ, rfl⟩)
    · obtain ⟨ν, rfl⟩ : μ ∈ Set.range (Sᶜ.orderEmbOfFin rfl) := by simpa using hμ
      exact Or.inl (basicEquation_removeBases hS ν ▸
        (Ω.removeBases S hS).basicEquation_mem_equations ν)
  · exact Or.inl (coeffEquation_removeBases hS b ▸
      (Ω.removeBases S hS).coeffEquation_mem_equations hb)
  · by_cases hμ : c.2.1 ∈ S
    · exact Or.inr (Or.inr ⟨c, ⟨hc, hμ⟩, rfl⟩)
    · obtain ⟨ν, hν⟩ : c.2.1 ∈ Set.range (Sᶜ.orderEmbOfFin rfl) := by simpa using hμ
      have hc' : (c.1, ν, c.2.2) ∈ (Ω.removeBases S hS).connections := by
        simpa [hν] using hc
      exact Or.inl (by simpa [hν] using
        (Ω.removeBases S hS).boundaryEquation_mem_equations hc')

/-! ### Formal consistency and group solutions -/

/-- Removing bases preserves formal consistency. -/
theorem IsFormallyConsistent.removeBases (hΩ : Ω.IsFormallyConsistent) :
    (Ω.removeBases S hS).IsFormallyConsistent where
  disjoint_of_sign_ne ν h := by
    simpa using hΩ.disjoint_of_sign_ne (Sᶜ.orderEmbOfFin rfl ν) (by simpa using h)
  connections_monotone_or_antitone c hc c' hc' h hp := by
    simpa using hΩ.connections_monotone_or_antitone _ ((mem_connections_removeBases hS).1 hc) _
      ((mem_connections_removeBases hS).1 hc') (by simp [h]) hp
  eq_of_left_eq c hc h :=
    hΩ.eq_of_left_eq _ ((mem_connections_removeBases hS).1 hc) (by simpa using h)
  label_eq := hΩ.label_eq
  connections_adjacent b hb c hc c' hc' h hp hp' :=
    hΩ.connections_adjacent b hb _ ((mem_connections_removeBases hS).1 hc) _
      ((mem_connections_removeBases hS).1 hc') (by simp [h]) hp hp'

/-- The system of the result is a subsystem of `Ω*`. -/
theorem toSystem_removeBases_subset : (Ω.removeBases S hS).toSystem ⊆ Ω.toSystem := by
  intro w hw
  obtain ⟨e, he, rfl⟩ := (mem_toSystem_iff _).1 hw
  exact (mem_toSystem_iff _).2 ⟨e, equations_removeBases_subset hS he, rfl⟩

/-- Every group solution of `Ω*` is a group solution of the system of the result. -/
theorem V_toSystem_subset_removeBases {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι Ω.toSystem ⊆ V ι (Ω.removeBases S hS).toSystem :=
  V_antitone ι (toSystem_removeBases_subset hS)

/-- If the basic equations of the bases of `S` and the boundary equations of the connections
through them have identical sides, every group solution of the system of the result is a group
solution of `Ω*`. -/
theorem V_toSystem_removeBases_subset {H : Type*} [Group H] (ι : FreeGroup A →* H)
    (hb : ∀ μ ∈ S, (Ω.basicEquation μ).1 = (Ω.basicEquation μ).2)
    (hc : ∀ c ∈ Ω.connections, c.2.1 ∈ S → (Ω.boundaryEquation c).1 = (Ω.boundaryEquation c).2) :
    V ι (Ω.removeBases S hS).toSystem ⊆ V ι Ω.toSystem := by
  intro v hv
  rw [mem_V_toSystem_iff] at hv ⊢
  intro e he
  rcases equations_subset_union_removeBases hS he with he | ⟨μ, hμ, rfl⟩ | ⟨c, ⟨hc', hμ⟩, rfl⟩
  · exact hv e he
  · rw [hb μ hμ]
  · rw [hc c hc' hμ]

/-! ### Solutions after removing bases -/

namespace Solution

variable (U : Ω.Solution)

/-- A solution of `Ω` is a solution of `Ω` with the bases of `S` removed, with the same words. -/
def removeBases : (Ω.removeBases S hS).Solution where
  word := U.word
  isReduced_word := U.isReduced_word
  word_ne_nil := U.word_ne_nil
  isReduced_subst e he := U.isReduced_subst e (equations_removeBases_subset hS he)
  subst_eq e he := U.subst_eq e (equations_removeBases_subset hS he)

/-- Removing bases keeps the words of a solution. -/
@[simp]
theorem removeBases_word : (U.removeBases hS).word = U.word :=
  (rfl)

/-- Removing bases keeps the point of a solution. -/
@[simp]
theorem removeBases_point : (U.removeBases hS).point = U.point := by
  ext k
  simp

/-- Removing bases keeps the positions of the boundaries in the words of a solution. -/
@[simp]
theorem removeBases_prefixLength : (U.removeBases hS).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

end Solution

/-! ### Removing a pair of dual bases -/

variable (Ω) in
/-- A base and its dual form a set of bases closed under duality. -/
theorem dual_mem_pair (μ : Fin Ω.numBases) :
    ∀ ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases)), Ω.dual ν ∈ ({μ, Ω.dual μ} : Finset _) := by
  simp [Ω.dual_involutive μ]

variable (Ω) in
/-- Remove a pair of dual variable bases `μ, Δ(μ)`, together with all boundary connections
through them. -/
abbrev removePair (μ : Fin Ω.numBases) : GenEq A :=
  Ω.removeBases {μ, Ω.dual μ} (Ω.dual_mem_pair μ)

/-- Removing a pair of distinct dual bases leaves `numBases - 2` bases. -/
theorem numBases_removePair {μ : Fin Ω.numBases} (h : μ ≠ Ω.dual μ) :
    (Ω.removePair μ).numBases = Ω.numBases - 2 := by
  rw [numBases_removeBases, Finset.card_pair h]

/-- If no boundary connection passes through `μ`, then `Ω*` presents the same group as the system
of `Ω` with `μ, Δ(μ)` removed together with the basic equation of `μ`, or with that of `Δ(μ)`. -/
theorem normalClosure_toSystem_eq_insert_removePair {μ : Fin Ω.numBases}
    (hc : ∀ c ∈ Ω.connections, c.2.1 ≠ μ) {ν : Fin Ω.numBases} (hν : ν = μ ∨ ν = Ω.dual μ) :
    Subgroup.normalClosure Ω.toSystem = Subgroup.normalClosure (insert
      (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation ν).1 *
        (FreeGroup.mk (Ω.basicEquation ν).2)⁻¹)) (Ω.removePair μ).toSystem) := by
  refine le_antisymm (Subgroup.normalClosure_le_normal fun t ht => ?_)
    (Subgroup.normalClosure_mono (Set.insert_subset ((mem_toSystem_iff _).2
      ⟨_, Ω.basicEquation_mem_equations ν, rfl⟩) (toSystem_removeBases_subset _)))
  obtain ⟨e, he, rfl⟩ := (mem_toSystem_iff _).1 ht
  rcases equations_subset_union_removeBases (Ω.dual_mem_pair μ) he with
    he | ⟨ν', hν', rfl⟩ | ⟨c, ⟨hc', hcμ⟩, rfl⟩
  · exact Subgroup.subset_normalClosure
      (Set.mem_insert_of_mem _ ((mem_toSystem_iff _).2 ⟨e, he, rfl⟩))
  · have hν'' : ν' = ν ∨ ν' = Ω.dual ν := by
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hν'
      rcases hν with rfl | rfl <;> rcases hν' with rfl | rfl <;> simp [Ω.dual_involutive _]
    rcases hν'' with rfl | rfl
    · exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
    · have hinv : EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation (Ω.dual ν)).1 *
          (FreeGroup.mk (Ω.basicEquation (Ω.dual ν)).2)⁻¹) =
          (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.basicEquation ν).1 *
            (FreeGroup.mk (Ω.basicEquation ν).2)⁻¹))⁻¹ := by
        simp only [basicEquation_fst, basicEquation_snd, Ω.dual_involutive ν, map_mul, map_inv,
          mul_inv_rev, inv_inv]
      rw [hinv]
      exact inv_mem (Subgroup.subset_normalClosure (Set.mem_insert _ _))
  · -- A connection through `Δ(μ)` has a dual connection through `μ`.
    rcases Finset.mem_insert.1 hcμ with hcμ | hcμ
    · exact absurd hcμ (hc c hc')
    · exact absurd (by rw [Finset.mem_singleton.1 hcμ, Ω.dual_involutive])
        (hc _ (Ω.dual_mem_connections c hc'))

/-- A solution of `Ω` as a solution of `Ω` with a pair of dual bases `μ, Δ(μ)` removed, with the
same words. -/
abbrev Solution.removePair (U : Ω.Solution) (μ : Fin Ω.numBases) : (Ω.removePair μ).Solution :=
  U.removeBases (Ω.dual_mem_pair μ)

end GenEq

end TauCeti
