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
open FreeGroup (substituteVars)

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

include hp hq in
/-- A solution of `Ω` which satisfies the boundary equation of `(p, μ, q)` satisfies every
equation of `Ω` with the boundary connection `(p, μ, q)` added, with both sides reduced as
written. -/
private theorem isReduced_and_eq_of_mem_equations_addConnection (U : Ω.Solution)
    (h : substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1 =
      substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2) :
    ∀ e ∈ (Ω.addConnection p μ q hp hq).equations,
      (FreeGroup.IsReduced (substituteVars U.word e.1) ∧
        FreeGroup.IsReduced (substituteVars U.word e.2)) ∧
        substituteVars U.word e.1 = substituteVars U.word e.2 := by
  obtain ⟨hp₁, hp₂⟩ := Ω.crosses_iff.1 hp
  obtain ⟨hq₁, hq₂⟩ := Ω.crosses_iff.1 hq
  have hp₁' : Ω.left (Ω.dual (Ω.dual μ)) ≤ p := by rw [Ω.dual_involutive μ]; exact hp₁.le
  have hp₂' : p ≤ Ω.right (Ω.dual (Ω.dual μ)) := by rw [Ω.dual_involutive μ]; exact hp₂.le
  rw [equations_addConnection]
  rintro e (he | rfl | rfl)
  · exact ⟨U.isReduced_subst e he, U.subst_eq e he⟩
  · exact ⟨⟨U.isReduced_substituteVars_boundaryEquation_fst hp₂.le,
      U.isReduced_substituteVars_boundaryEquation_snd hq₁.le hq₂.le⟩, h⟩
  · exact ⟨⟨U.isReduced_substituteVars_boundaryEquation_fst hq₂.le,
      U.isReduced_substituteVars_boundaryEquation_snd hp₁' hp₂'⟩,
      (U.substituteVars_boundaryEquation_dual_eq_iff hp₁.le hp₂.le hq₁.le hq₂.le).2 h⟩

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
  rw [← U.substituteVars_boundaryEquation_eq_iff (Ω.crosses_iff.1 hp).2.le]
  refine ⟨fun ⟨U', hU'⟩ => ?_, fun h => ?_⟩
  · have he := U'.subst_eq _ ((Ω.addConnection p μ q hp hq).boundaryEquation_mem_equations
      ((mem_connections_addConnection hp hq).2 (Or.inr (Or.inl rfl))))
    rwa [boundaryEquation_addConnection, hU'] at he
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
