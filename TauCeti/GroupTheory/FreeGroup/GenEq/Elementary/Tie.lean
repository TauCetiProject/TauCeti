/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
import Mathlib.Data.Fin.VecNotation

/-!
# Introduction of a boundary connection

The elementary transformation ET5 of Makanin's process (Kharlampovich–Myasnikov, §5.1) ties a
boundary `p` inside a variable base `μ` of a generalised equation `Ω` to the dual base `Δ(μ)`.
Its first kind adds, for a boundary `q` inside `Δ(μ)`, the boundary connection `(p, μ, q)`
together with its dual `(q, Δ(μ), p)`. Writing `Ω_q` for the result
(`TauCeti.GenEq.addConnection`):

* `Ω_q` has the same items as `Ω`, and its equations are those of `Ω` together with the boundary
  equations of the two new connections (`TauCeti.GenEq.equations_addConnection`);
* so every point of `Ω_q*` is a point of `Ω*` (`TauCeti.GenEq.V_toSystem_addConnection_subset`),
  and the identity on the items induces a surjective `F(A)`-homomorphism
  `F_{R(Ω)} → F_{R(Ω_q)}` of coordinate groups (`TauCeti.GenEq.addConnectionHom`,
  `TauCeti.GenEq.addConnectionHom_surjective`); it need not be injective, as the example at the
  end of the file shows;
* every solution of `Ω_q` is a solution of `Ω` with the same words
  (`TauCeti.GenEq.Solution.ofAddConnection`), and its homomorphism composed with
  `F_{R(Ω)} → F_{R(Ω_q)}` is the homomorphism of that solution of `Ω`
  (`TauCeti.GenEq.toHom_comp_addConnectionHom`);
* a solution `U` of `Ω` is a solution of `Ω_q` exactly when `p` and `q` lie at the same position
  in the words `U[α(μ), β(μ)]` and `U[α(Δμ), β(Δμ)]`, counted from the left end of both when
  `ε(μ) = ε(Δμ)` and from the right end of `Δ(μ)` otherwise
  (`TauCeti.GenEq.exists_solution_addConnection_iff`; Kharlampovich–Myasnikov–Serbin, ET5(a)).

The source applies ET5 to a boundary `p` that is not yet tied through `μ`, and keeps `Ω_q` only
when it is formally consistent. Both conditions concern which results are kept as successors of
`Ω`; neither is needed for the statements here, and neither is imposed.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET5.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET5.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §11.3, ET5.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars substituteVars_append substituteVars_invRev)

section AddConnection

variable {A : Type*} (Ω : GenEq A)

/-- Add the boundary connection `(p, μ, q)` and its dual `(q, Δ(μ), p)`, for a boundary `p`
inside `μ` and a boundary `q` inside `Δ(μ)`. -/
abbrev addConnection (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (q : Fin (Ω.numItems + 1))
    (hp : Ω.Crosses p μ) (hq : Ω.Crosses q (Ω.dual μ)) : GenEq A :=
  { Ω with
    connections := Ω.connections ∪ {(p, μ, q), (q, Ω.dual μ, p)}
    bounds_of_mem_connections := by
      intro c hc
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hc | rfl | rfl
      · exact Ω.bounds_of_mem_connections c hc
      · exact and_assoc.1 ⟨Ω.crosses_iff.1 hp, Ω.crosses_iff.1 hq⟩
      · simpa [Ω.dual_involutive μ] using and_assoc.1 ⟨Ω.crosses_iff.1 hq, Ω.crosses_iff.1 hp⟩
    dual_mem_connections := by
      intro c hc
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hc ⊢
      rcases hc with hc | rfl | rfl
      · exact Or.inl (Ω.dual_mem_connections c hc)
      · exact Or.inr (Or.inr rfl)
      · simp [Ω.dual_involutive μ] }

variable {Ω} {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} {q : Fin (Ω.numItems + 1)}
  (hp : Ω.Crosses p μ) (hq : Ω.Crosses q (Ω.dual μ))

/-- The boundary connections of `Ω` with `(p, μ, q)` added are those of `Ω`, `(p, μ, q)` and
its dual `(q, Δ(μ), p)`. -/
theorem mem_connections_addConnection
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} :
    c ∈ (Ω.addConnection p μ q hp hq).connections ↔
      c ∈ Ω.connections ∨ c = (p, μ, q) ∨ c = (q, Ω.dual μ, p) := by
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

/-- The segments `h[i, j] ^ ±1` only depend on the items, which adding a boundary connection
keeps. -/
@[simp]
theorem segment_addConnection (i j : ℕ) (s : Bool) :
    (Ω.addConnection p μ q hp hq).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- Adding a boundary connection keeps the basic equations. -/
@[simp]
theorem basicEquation_addConnection (ν : Fin Ω.numBases) :
    (Ω.addConnection p μ q hp hq).basicEquation ν = Ω.basicEquation ν :=
  Prod.ext (by simp) (by simp)

/-- Adding a boundary connection keeps the coefficient equations. -/
@[simp]
theorem coeffEquation_addConnection (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.addConnection p μ q hp hq).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- Adding a boundary connection keeps the boundary equation of every triple. -/
@[simp]
theorem boundaryEquation_addConnection
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.addConnection p μ q hp hq).boundaryEquation c = Ω.boundaryEquation c := by
  refine Prod.ext (by simp) ?_
  by_cases h : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, h]

/-- The equations of `Ω` with the boundary connection `(p, μ, q)` added are those of `Ω`
together with the boundary equations of `(p, μ, q)` and of its dual `(q, Δ(μ), p)`. -/
theorem equations_addConnection : (Ω.addConnection p μ q hp hq).equations =
    Ω.equations ∪ {Ω.boundaryEquation (p, μ, q), Ω.boundaryEquation (q, Ω.dual μ, p)} := by
  ext e
  simp only [mem_equations_iff, basicEquation_addConnection, coeffEquation_addConnection,
    boundaryEquation_addConnection, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

/-- The equations of `Ω` are equations of `Ω` with a boundary connection added. -/
theorem equations_subset_addConnection : Ω.equations ⊆ (Ω.addConnection p μ q hp hq).equations :=
  (equations_addConnection hp hq).symm ▸ Set.subset_union_left

/-- **ET5, first kind, on group solutions.** Every point of the system of `Ω` with a boundary
connection added is a point of `Ω*`, in every group `H` receiving `F(A)` through `ι`. -/
theorem V_toSystem_addConnection_subset {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι (Ω.addConnection p μ q hp hq).toSystem ⊆ V ι Ω.toSystem :=
  V_antitone ι fun _ hw => by
    obtain ⟨e, he, rfl⟩ := (mem_toSystem_iff _).1 hw
    exact (mem_toSystem_iff _).2 ⟨e, equations_subset_addConnection hp hq he, rfl⟩

/-- **ET5, first kind.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω_q)}` induced by the identity
on the items, where `Ω_q` is `Ω` with the boundary connection `(p, μ, q)` added. -/
def addConnectionHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.addConnection p μ q hp hq).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_addConnection_subset hp hq _)

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω_q)}` of ET5 is the identity on the words in the
items. -/
-- Not `@[simp]`: the reducible `addConnection` in the codomain keeps `simp` from indexing this
-- lemma uninstantiated, so it is used through `rw`.
theorem addConnectionHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    addConnectionHom hp hq (w : Ω.coordGroup) = (w : (Ω.addConnection p μ q hp hq).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- **ET5, first kind.** The homomorphism `F_{R(Ω)} → F_{R(Ω_q)}` is surjective. -/
theorem addConnectionHom_surjective : Function.Surjective (addConnectionHom hp hq) :=
  CoordGroup.homOfVSubset_surjective _

namespace Solution

/-- A solution of `Ω` with a boundary connection added is a solution of `Ω`, with the same
words. -/
def ofAddConnection (U : (Ω.addConnection p μ q hp hq).Solution) : Ω.Solution where
  word := U.word
  isReduced_word := U.isReduced_word
  word_ne_nil := U.word_ne_nil
  isReduced_subst e he := U.isReduced_subst e (equations_subset_addConnection hp hq he)
  subst_eq e he := U.subst_eq e (equations_subset_addConnection hp hq he)

/-- A solution of `Ω` with a boundary connection added keeps its words as a solution of `Ω`. -/
@[simp]
theorem ofAddConnection_word (U : (Ω.addConnection p μ q hp hq).Solution) :
    (U.ofAddConnection hp hq).word = U.word :=
  (rfl)

end Solution

/-- The homomorphism of a solution of `Ω_q` composed with `F_{R(Ω)} → F_{R(Ω_q)}` is the
homomorphism of the same solution of `Ω`. -/
theorem toHom_comp_addConnectionHom (U : (Ω.addConnection p μ q hp hq).Solution) :
    U.toHom.comp (addConnectionHom hp hq) = (U.ofAddConnection hp hq).toHom := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, addConnectionHom_mk]
  simp

namespace Solution

variable (U : Ω.Solution)

/-- Below a base, the words of a solution are reduced as written: `U[i, j]` is a factor of
`U[α(ν), β(ν)]` for `α(ν) ≤ i ≤ j ≤ β(ν)`. -/
private theorem isReduced_substituteVars_segment_of_le (ν : Fin Ω.numBases) {i j : ℕ}
    (hi : Ω.left ν ≤ i) (hij : i ≤ j) (hj : j ≤ Ω.right ν) :
    FreeGroup.IsReduced (substituteVars U.word (Ω.segment i j true)) := by
  have h := U.isReduced_substituteVars_segment ν
  rw [← Ω.segment_append hi (hij.trans hj) (Ω.right ν).is_le,
    ← Ω.segment_append hij hj (Ω.right ν).is_le, substituteVars_append,
    substituteVars_append, ← List.append_assoc] at h
  exact h.infix (List.infix_append _ _ _)

/-- When `ε(μ) = ε(Δμ)`, a solution assigns the same word to the bases `μ` and `Δ(μ)`. -/
private theorem substituteVars_segment_eq_of_sign_eq (hs : Ω.sign μ = Ω.sign (Ω.dual μ)) :
    substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) =
      substituteVars U.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true) := by
  have e := U.subst_eq _ (Ω.basicEquation_mem_equations μ)
  rw [basicEquation_fst, basicEquation_snd, ← hs] at e
  cases h : Ω.sign μ <;> rw [h] at e
  · rw [segment_false, segment_false, substituteVars_invRev, substituteVars_invRev] at e
    exact FreeGroup.invRev_injective e
  · exact e

/-- When `ε(μ) ≠ ε(Δμ)`, a solution assigns to the base `μ` the formal inverse of the word of
`Δ(μ)`. -/
private theorem substituteVars_segment_eq_invRev_of_sign_ne (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) :
    substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) = FreeGroup.invRev
      (substituteVars U.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
  have e := U.subst_eq _ (Ω.basicEquation_mem_equations μ)
  rw [basicEquation_fst, basicEquation_snd] at e
  cases h : Ω.sign μ <;> cases h' : Ω.sign (Ω.dual μ) <;> rw [h, h'] at e <;>
    simp only [h, h', ne_eq, not_true_eq_false] at hs
  · rw [segment_false, substituteVars_invRev] at e
    rw [← e, FreeGroup.invRev_invRev]
  · rwa [segment_false, substituteVars_invRev] at e

include hp hq in
/-- Both sides of the boundary equation of `(p, μ, q)` are reduced as written under a solution:
they are factors of the words of `μ` and `Δ(μ)`. -/
private theorem isReduced_substituteVars_boundaryEquation :
    FreeGroup.IsReduced (substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1) ∧
      FreeGroup.IsReduced (substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2) := by
  obtain ⟨hp₁, hp₂⟩ := Ω.crosses_iff.1 hp
  obtain ⟨hq₁, hq₂⟩ := Ω.crosses_iff.1 hq
  rw [boundaryEquation_fst]
  refine ⟨U.isReduced_substituteVars_segment_of_le μ le_rfl hp₁.le hp₂.le, ?_⟩
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs]
    exact U.isReduced_substituteVars_segment_of_le _ le_rfl hq₁.le hq₂.le
  · rw [Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      isReduced_substituteVars_segment_iff]
    exact U.isReduced_substituteVars_segment_of_le _ hq₁.le hq₂.le le_rfl

include hp hq in
/-- The boundary equation of `(p, μ, q)` holds letter by letter under a solution exactly when
`p` and `q` lie at the same position of the words of `μ` and `Δ(μ)`. -/
private theorem substituteVars_boundaryEquation_eq_iff :
    substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1 =
        substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2 ↔
      U.prefixLength p - U.prefixLength (Ω.left μ) =
        if Ω.sign μ = Ω.sign (Ω.dual μ) then
          U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ))
        else U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength q := by
  obtain ⟨hp₁, hp₂⟩ := Ω.crosses_iff.1 hp
  obtain ⟨hq₁, hq₂⟩ := Ω.crosses_iff.1 hq
  have lp := U.length_substituteVars_segment_add_prefixLength true hp₁.le
  have lq₁ := U.length_substituteVars_segment_add_prefixLength true hq₁.le
  have lq₂ := U.length_substituteVars_segment_add_prefixLength true hq₂.le
  -- Cut the words of `μ` at `p` and of `Δ(μ)` at `q`.
  have sμ := congrArg (substituteVars U.word) (Ω.segment_append hp₁.le hp₂.le (Ω.right μ).is_le)
  have sΔ := congrArg (substituteVars U.word)
    (Ω.segment_append hq₁.le hq₂.le (Ω.right (Ω.dual μ)).is_le)
  rw [substituteVars_append] at sμ sΔ
  rw [boundaryEquation_fst]
  split_ifs with hs
  · have hb := U.substituteVars_segment_eq_of_sign_eq hs
    rw [← sμ, ← sΔ] at hb
    rw [Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs]
    dsimp only
    refine ⟨fun h => ?_, fun h => (List.append_inj hb (by lia)).1⟩
    have := congrArg List.length h
    lia
  · have hb := U.substituteVars_segment_eq_invRev_of_sign_ne hs
    rw [← sμ, ← sΔ, FreeGroup.invRev_append] at hb
    rw [Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs, segment_false,
      substituteVars_invRev]
    dsimp only
    refine ⟨fun h => ?_, fun h => (List.append_inj hb ?_).1⟩
    · have := congrArg List.length h
      rw [FreeGroup.invRev_length] at this
      lia
    · rw [FreeGroup.invRev_length]
      lia

include hp hq in
/-- If a solution places `p` and `q` at the same position of the words of `μ` and `Δ(μ)`, it
places `q` and `p` at the same position of the words of `Δ(μ)` and `Δ(Δ(μ)) = μ`, since these
words have the same length. -/
private theorem prefixLength_sub_dual
    (h : U.prefixLength p - U.prefixLength (Ω.left μ) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ))
      else U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength q) :
    U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ)) =
      if Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) then
        U.prefixLength p - U.prefixLength (Ω.left (Ω.dual (Ω.dual μ)))
      else U.prefixLength (Ω.right (Ω.dual (Ω.dual μ))) - U.prefixLength p := by
  have e := congrArg List.length (U.subst_eq _ (Ω.basicEquation_mem_equations μ))
  rw [basicEquation_fst, basicEquation_snd] at e
  have l₁ := U.length_substituteVars_segment_add_prefixLength (Ω.sign μ) (Ω.left_lt_right μ).le
  have l₂ := U.length_substituteVars_segment_add_prefixLength (Ω.sign (Ω.dual μ))
    (Ω.left_lt_right (Ω.dual μ)).le
  have m₁ := U.prefixLength_mono (Ω.crosses_iff.1 hp).1.le
  have m₂ := U.prefixLength_mono (Ω.crosses_iff.1 hp).2.le
  have m₃ := U.prefixLength_mono (Ω.crosses_iff.1 hq).1.le
  have m₄ := U.prefixLength_mono (Ω.crosses_iff.1 hq).2.le
  simp only [Ω.dual_involutive μ, eq_comm (a := Ω.sign (Ω.dual μ))]
  split_ifs at h ⊢ <;> lia

include hp hq in
/-- If a solution places `p` and `q` at the same position of the words of `μ` and `Δ(μ)`, it
satisfies every equation of `Ω` with the boundary connection `(p, μ, q)` added, with both sides
reduced as written. -/
private theorem isReduced_and_eq_of_mem_equations_addConnection
    (h : U.prefixLength p - U.prefixLength (Ω.left μ) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ))
      else U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength q) :
    ∀ e ∈ (Ω.addConnection p μ q hp hq).equations,
      (FreeGroup.IsReduced (substituteVars U.word e.1) ∧
        FreeGroup.IsReduced (substituteVars U.word e.2)) ∧
        substituteVars U.word e.1 = substituteVars U.word e.2 := by
  have hp' : Ω.Crosses p (Ω.dual (Ω.dual μ)) := by rwa [Ω.dual_involutive μ]
  rw [equations_addConnection]
  rintro e (he | rfl | rfl)
  · exact ⟨U.isReduced_subst e he, U.subst_eq e he⟩
  · exact ⟨U.isReduced_substituteVars_boundaryEquation hp hq,
      (U.substituteVars_boundaryEquation_eq_iff hp hq).2 h⟩
  · exact ⟨U.isReduced_substituteVars_boundaryEquation hq hp',
      (U.substituteVars_boundaryEquation_eq_iff hq hp').2 (U.prefixLength_sub_dual hp hq h)⟩

end Solution

/-- A solution of `Ω` is a solution of `Ω` with the boundary connection `(p, μ, q)` added
exactly when the boundaries `p` of `μ` and `q` of `Δ(μ)` lie at the same position of the word of
`μ`: `|U[α(μ), p]| = |U[α(Δμ), q]|` when `ε(μ) = ε(Δμ)`, and `|U[α(μ), p]| = |U[q, β(Δμ)]|`
otherwise. -/
theorem exists_solution_addConnection_iff (U : Ω.Solution) :
    (∃ U' : (Ω.addConnection p μ q hp hq).Solution, U'.word = U.word) ↔
      U.prefixLength p - U.prefixLength (Ω.left μ) =
        if Ω.sign μ = Ω.sign (Ω.dual μ) then
          U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ))
        else U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength q := by
  refine ⟨fun ⟨U', hU'⟩ => ?_, fun h => ?_⟩
  · have he := U'.subst_eq _ ((Ω.addConnection p μ q hp hq).boundaryEquation_mem_equations
      ((mem_connections_addConnection hp hq).2 (Or.inr (Or.inl rfl))))
    rw [boundaryEquation_addConnection, hU'] at he
    exact (U.substituteVars_boundaryEquation_eq_iff hp hq).1 he
  have key := U.isReduced_and_eq_of_mem_equations_addConnection hp hq h
  exact ⟨⟨U.word, U.isReduced_word, U.word_ne_nil, fun e he => (key e he).1,
    fun e he => (key e he).2⟩, rfl⟩

end AddConnection

/-! ### Example -/

/-- The generalised equation `h₀h₁ = h₂h₃`: four items and the dual bases `[0, 2]`, `[2, 4]`,
both of sign `+1`. -/
private abbrev pairExample : GenEq (Fin 2) where
  numItems := 4
  numBases := 2
  left := ![0, 2]
  right := ![2, 4]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The homomorphism of ET5 of the first kind can be a proper quotient: adding the boundary
connection `(1, μ, 3)` to `h₀h₁ = h₂h₃` adds the equation `h₀ = h₂`, which holds in
`F_{R(Ω_q)}` but not in `F_{R(Ω)}` (the point `(a, 1, 1, a)` of `Ω*` separates `h₀` from `h₂`). -/
example : ¬ Function.Injective
    (addConnectionHom (Ω := pairExample) (p := 1) (μ := 0) (q := 3) (by decide) (by decide)) := by
  intro hinj
  have hb : pairExample.boundaryEquation (1, 0, 3) =
      ([(Sum.inl 0, true)], [(Sum.inl 2, true)]) := by
    rw [Prod.ext_iff, boundaryEquation_fst, pairExample.boundaryEquation_snd_of_sign_eq rfl,
      segment_true, segment_true]
    decide
  -- In `F_{R(Ω_q)}` the items `h₀` and `h₂` are equal.
  have h₀₂ := hinj (a₁ := ((inr (FreeGroup.of 0) : GX (FreeGroup (Fin 2)) (Fin 4)) :
      pairExample.coordGroup)) (a₂ := ((inr (FreeGroup.of 2) : GX (FreeGroup (Fin 2)) (Fin 4)) :
      pairExample.coordGroup)) (by
    rw [addConnectionHom_mk, addConnectionHom_mk, QuotientGroup.eq, mem_Rad]
    intro v hv
    have := (mem_V_toSystem_iff _).1 hv _ (boundaryEquation_mem_equations _
      ((mem_connections_addConnection _ _).2 (Or.inr (Or.inl rfl))))
    rw [boundaryEquation_addConnection, hb] at this
    simpa [inv_mul_eq_one] using this)
  -- In `F_{R(Ω)}` they are separated by the point `(a, 1, 1, a)` of `Ω*`.
  have hv : (![FreeGroup.of 0, 1, 1, FreeGroup.of 0] : Fin 4 → FreeGroup (Fin 2)) ∈
      V (MonoidHom.id (FreeGroup (Fin 2))) pairExample.toSystem := by
    rw [mem_V_toSystem_iff, forall_mem_equations]
    refine ⟨?_, fun _ hb => absurd hb (Finset.notMem_empty _),
      fun _ hc => absurd hc (Finset.notMem_empty _)⟩
    simp only [basicEquation_fst, basicEquation_snd, segment_true]
    decide
  have := congrArg (CoordGroup.evalGHom _ hv) h₀₂
  simp at this

end GenEq

end TauCeti
