/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.SplitItem
import Mathlib.Data.Fin.VecNotation

/-!
# Introduction of a boundary

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

Its second kind ties `p` to a new boundary: for an item `h_k` of `Δ(μ)`, split `h_k` into
`h′_k h′_{k+1}` by a new boundary (`TauCeti.GenEq.splitItem`) and add the boundary connection from
`p` to it. Writing `Ω′` for the result (`TauCeti.GenEq.tieNew`), and when `h_k` carries no
constant base:

* the substitution `h_k ↦ h′_k h′_{k+1}` maps the points of `Ω′*` bijectively onto the points of
  `Ω*`, in every `F(A)`-group (`TauCeti.GenEq.bijOn_wordMap_tieNew`): the new boundary equation
  determines `h′_k` from the image, and the equation of the dual connection follows from it and
  the basic equation of `μ`;
* so the substitution induces an `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}`
  (`TauCeti.GenEq.tieNewHom`, `TauCeti.GenEq.tieNewHom_bijective`);
* every solution of `Ω′` gives a solution of `Ω`, the word of `h_k` being the concatenation of
  the words of `h′_k` and `h′_{k+1}` (`TauCeti.GenEq.Solution.ofTieNew`), and its homomorphism
  composed with `F_{R(Ω)} → F_{R(Ω′)}` is the homomorphism of that solution of `Ω`
  (`TauCeti.GenEq.toHom_comp_tieNewHom`); the boundaries of `Ω` keep their positions in the words
  (`TauCeti.GenEq.Solution.prefixLength_ofTieNew`);
* a solution `U` of `Ω` comes from a solution of `Ω′` exactly when the position of `p` in the
  word of `μ`, read in the word of `Δ(μ)` from its left end when `ε(μ) = ε(Δμ)` and from its right
  end otherwise, lies strictly inside the word of `h_k`
  (`TauCeti.GenEq.exists_solution_tieNew_iff`; Kharlampovich–Myasnikov–Serbin, ET5(b)).

The source does not restrict the split item; here it must carry no constant base. A constant
base spans one item, so the substitution `h_k ↦ h′_k h′_{k+1}` does not respect its coefficient
equation; and no solution is lost, since the one-letter word of a constant item has no interior
position.

The source applies ET5 to a boundary `p` that is not yet tied through `μ`, and keeps a result
only when it is formally consistent. Both conditions concern which results are kept as
successors of `Ω`; neither is needed for the statements here, and neither is imposed.

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

section TieNew

variable {A : Type*} {Ω : GenEq A} {k : Fin Ω.numItems}

/-! ### Introducing a boundary -/

variable (Ω) in
/-- Tie the boundary `p` inside `μ` to a new boundary splitting the item `h_k` of `Δ(μ)` (ET5,
second kind). -/
abbrev tieNew (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (k : Fin Ω.numItems)
    (hp : Ω.Crosses p μ) (hk : k ∈ Ω.baseItems (Ω.dual μ)) : GenEq A :=
  (Ω.splitItem k).addConnection (k.succ.castSucc.succAbove p) μ k.succ.castSucc
    (crosses_splitItem_succAbove_iff.2 hp) (crosses_splitItem_succ_castSucc_iff.2 hk)

variable {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} (hp : Ω.Crosses p μ)
  (hk : k ∈ Ω.baseItems (Ω.dual μ)) (hk' : ¬ Ω.IsConstantItem k)

variable (Ω) in
/-- The word in the old items to which the new boundary connection of `Ω.tieNew p μ k hp hk`
equates `h′_k`: `h[α(Δμ), k]⁻¹ h[α(μ), p]` when `ε(μ) = ε(Δμ)`, and `h[k, β(Δμ)] h[α(μ), p]`
otherwise. -/
private def tieList (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (k : Fin Ω.numItems) :
    List ((Fin Ω.numItems ⊕ A) × Bool) :=
  if Ω.sign μ = Ω.sign (Ω.dual μ) then
    Ω.segment (Ω.left (Ω.dual μ)) k false ++ Ω.segment (Ω.left μ) p true
  else Ω.segment k (Ω.right (Ω.dual μ)) true ++ Ω.segment (Ω.left μ) p true

include hk in
/-- The boundary equation of the new connection of `Ω.tieNew p μ k hp hk` holds at a tuple
exactly when the value of `h′_k` is the value of `tieList` at the image of the tuple under
`h_k ↦ h′_k h′_{k+1}`. -/
private theorem lift_mk_boundaryEquation_tieNew_iff {H : Type*} [Group H] (ι : FreeGroup A →* H)
    (v : Fin (Ω.numItems + 1) → H) :
    FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk ((Ω.splitItem k).boundaryEquation
        (k.succ.castSucc.succAbove p, μ, k.succ.castSucc)).1) =
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk ((Ω.splitItem k).boundaryEquation
        (k.succ.castSucc.succAbove p, μ, k.succ.castSucc)).2) ↔
    v k.castSucc = FreeGroup.lift (Sum.elim (wordMap ι (Ω.splitWord k) v) (ι ∘ FreeGroup.of))
      (FreeGroup.mk (Ω.tieList p μ k)) := by
  have hv := lift_mk_splitList (k := k) ι v
  have hmul {β : Type _} (g : β → H) (l l' : List (β × Bool)) :
      FreeGroup.lift g (FreeGroup.mk (l ++ l')) =
        FreeGroup.lift g (FreeGroup.mk l) * FreeGroup.lift g (FreeGroup.mk l') := by
    rw [← FreeGroup.mul_mk, map_mul]
  -- Evaluation: `tieList = t h[α(μ), p]`, and the right side of the new equation is `t⁻¹ h′_k`,
  -- with `t = h[α(Δμ), k]⁻¹` when `ε(μ) = ε(Δμ)` and `t = h[k, β(Δμ)]` otherwise.
  obtain ⟨t, ht, hR⟩ : ∃ t, Ω.tieList p μ k = t ++ Ω.segment (Ω.left μ) p true ∧
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk ((Ω.splitItem k).boundaryEquation
        (k.succ.castSucc.succAbove p, μ, k.succ.castSucc)).2) =
      (FreeGroup.lift (Sum.elim (wordMap ι (Ω.splitWord k) v) (ι ∘ FreeGroup.of))
        (FreeGroup.mk t))⁻¹ * v k.castSucc := by
    by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
    · -- The right side is `h′[α(Δμ), k + 1] = h[α(Δμ), k] h′_k`.
      refine ⟨_, ite_eq_left hs, ?_⟩
      rw [(Ω.splitItem k).boundaryEquation_snd_of_sign_eq (c := (_, μ, _)) hs]
      dsimp only
      rw [segment_splitItem_succAbove_succ_castSucc (Ω.mem_baseItems.1 hk).1, hmul, hv,
        Ω.lift_mk_segment _ _ _ false]
      simp
    · -- The right side is `h′[k + 1, β(Δμ)]⁻¹`, where `h′_k h′[k + 1, β(Δμ)] = h[k, β(Δμ)]`.
      refine ⟨_, ite_eq_right hs, ?_⟩
      rw [(Ω.splitItem k).boundaryEquation_snd_of_sign_ne (c := (_, μ, _)) hs]
      dsimp only
      rw [(Ω.splitItem k).lift_mk_segment _ _ _ false, ← hv,
        ← cons_segment_splitItem_succ_castSucc_succAbove (Ω.mem_baseItems.1 hk).2,
        ← List.singleton_append, hmul]
      simp
  -- Group identity: `x = t⁻¹ h′_k ↔ h′_k = t x`.
  rw [hR, boundaryEquation_fst, segment_splitItem, hv, ht, hmul]
  exact eq_inv_mul_iff_mul_eq.trans eq_comm

include hp hk hk' in
/-- A tuple is a point of the system of `Ω.tieNew p μ k hp hk` exactly when its image under
`h_k ↦ h′_k h′_{k+1}` is a point of `Ω*` and its value at `h′_k` is the value of `tieList` at
that image. -/
private theorem mem_V_tieNew_iff {H : Type*} [Group H] (ι : FreeGroup A →* H)
    {v : Fin (Ω.numItems + 1) → H} :
    v ∈ V ι (Ω.tieNew p μ k hp hk).toSystem ↔ wordMap ι (Ω.splitWord k) v ∈ V ι Ω.toSystem ∧
      v k.castSucc = FreeGroup.lift (Sum.elim (wordMap ι (Ω.splitWord k) v) (ι ∘ FreeGroup.of))
        (FreeGroup.mk (Ω.tieList p μ k)) := by
  obtain ⟨hp₁, hp₂⟩ := (Ω.splitItem k).crosses_iff.1 (crosses_splitItem_succAbove_iff.2 hp)
  obtain ⟨hq₁, hq₂⟩ := (Ω.splitItem k).crosses_iff.1 (crosses_splitItem_succ_castSucc_iff.2 hk)
  rw [← mem_V_splitItem_iff hk', ← lift_mk_boundaryEquation_tieNew_iff hk ι v, mem_V_toSystem_iff,
    mem_V_toSystem_iff, equations_addConnection, Set.forall_mem_union, Set.forall_mem_insert,
    Set.forall_mem_singleton]
  -- The equation of the dual connection follows from the new one and the basic equation of `μ`.
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  exact ((Ω.splitItem k).lift_mk_boundaryEquation_dual_iff _ hp₁.le hp₂.le hq₁.le hq₂.le
    (h.1 _ ((Ω.splitItem k).basicEquation_mem_equations μ))).2 h.2

variable (Ω) in
/-- The inverse of the substitution `h_k ↦ h′_k h′_{k+1}` on the points of
`Ω.tieNew p μ k hp hk`, as a tuple of words in the old items: `h′_k ↦ tieList`,
`h′_{k+1} ↦ tieList⁻¹ h_k`, and every other item to the item with its old number. -/
private def tieWord (p : Fin (Ω.numItems + 1)) (μ : Fin Ω.numBases) (k : Fin Ω.numItems) :
    Fin (Ω.numItems + 1) → GX (FreeGroup A) (Fin Ω.numItems) :=
  Fin.insertNth (α := fun _ => GX (FreeGroup A) (Fin Ω.numItems)) k.castSucc
    (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.tieList p μ k)))
    (Function.update (fun j => inr (FreeGroup.of j)) k
      ((EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.tieList p μ k)))⁻¹ *
        inr (FreeGroup.of k)))

private theorem tieWord_castSucc : Ω.tieWord p μ k k.castSucc =
    EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.tieList p μ k)) := by
  rw [tieWord, Fin.insertNth_apply_same]

private theorem tieWord_succ : Ω.tieWord p μ k k.succ =
    (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.tieList p μ k)))⁻¹ *
      inr (FreeGroup.of k) := by
  rw [tieWord, ← Fin.succAbove_castSucc_self, Fin.insertNth_apply_succAbove, Function.update_self]

private theorem tieWord_succAbove {j : Fin Ω.numItems} (hj : j ≠ k) :
    Ω.tieWord p μ k (k.castSucc.succAbove j) = inr (FreeGroup.of j) := by
  rw [tieWord, Fin.insertNth_apply_succAbove, Function.update_of_ne hj]

/-- Substituting `tieWord` into `h_k ↦ h′_k h′_{k+1}` gives back every item. -/
private theorem eval_tieWord_splitWord (j : Fin Ω.numItems) :
    eval inl (Ω.tieWord p μ k) (Ω.splitWord k j) = inr (FreeGroup.of j) := by
  rw [eval_splitWord]
  rcases eq_or_ne j k with rfl | h
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ rfl, tieWord_castSucc, tieWord_succ,
      mul_inv_cancel_left]
  · rw [Fin.contractNth_apply_of_ne k.castSucc _ _ j (Fin.val_ne_of_ne h).symm,
      tieWord_succAbove h]

/-- The substitution `h_k ↦ h′_k h′_{k+1}` undoes `tieWord` on every tuple. -/
private theorem wordMap_splitWord_wordMap_tieWord {H : Type*} [Group H] (ι : FreeGroup A →* H)
    (v : Fin Ω.numItems → H) :
    wordMap ι (Ω.splitWord k) (wordMap ι (Ω.tieWord p μ k) v) = v := by
  simp only [wordMap_wordMap, eval_tieWord_splitWord, wordMap_id]

include hp hk hk' in
/-- `tieWord` maps the points of `Ω*` to points of the system of `Ω.tieNew p μ k hp hk`. -/
private theorem mapsTo_wordMap_tieWord {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    Set.MapsTo (wordMap ι (Ω.tieWord p μ k)) (V ι Ω.toSystem)
      (V ι (Ω.tieNew p μ k hp hk).toSystem) := fun v hv => by
  refine (mem_V_tieNew_iff hp hk hk' ι).2 ⟨by rwa [wordMap_splitWord_wordMap_tieWord], ?_⟩
  rw [wordMap_splitWord_wordMap_tieWord, wordMap_apply, tieWord_castSucc,
    EqIneqSystem.eval_toGX, EqIneqSystem.eval_eq_lift]

include hp hk hk' in
/-- On the points of the system of `Ω.tieNew p μ k hp hk`, `tieWord` undoes the substitution
`h_k ↦ h′_k h′_{k+1}`: the new boundary connection determines `h′_k`. -/
private theorem wordMap_tieWord_wordMap_splitWord {H : Type*} [Group H] (ι : FreeGroup A →* H)
    {v : Fin (Ω.numItems + 1) → H} (hv : v ∈ V ι (Ω.tieNew p μ k hp hk).toSystem) :
    wordMap ι (Ω.tieWord p μ k) (wordMap ι (Ω.splitWord k) v) = v := by
  have hk₀ := ((mem_V_tieNew_iff hp hk hk' ι).1 hv).2
  have hcs : FreeGroup.lift (Sum.elim (wordMap ι (Ω.splitWord k) v) (ι ∘ FreeGroup.of))
      (FreeGroup.mk (Ω.tieList p μ k)) = eval ι (wordMap ι (Ω.splitWord k) v)
        (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.tieList p μ k))) := by
    rw [EqIneqSystem.eval_toGX, EqIneqSystem.eval_eq_lift]
  funext x
  rcases Fin.eq_self_or_eq_succAbove k.castSucc x with rfl | ⟨j, rfl⟩
  · rw [wordMap_apply, tieWord_castSucc, ← hcs, ← hk₀]
  · rcases eq_or_ne j k with rfl | hj
    · rw [Fin.succAbove_castSucc_self, wordMap_apply, tieWord_succ, map_mul, map_inv, eval_inr_of,
        ← hcs, ← hk₀, wordMap_apply, eval_splitWord, Fin.contractNth_apply_of_eq _ _ _ _ rfl,
        inv_mul_cancel_left]
    · rw [wordMap_apply, tieWord_succAbove hj, eval_inr_of, wordMap_apply, eval_splitWord,
        Fin.contractNth_apply_of_ne k.castSucc _ _ j (Fin.val_ne_of_ne hj).symm]

include hk' in
/-- **ET5, second kind, on group solutions.** The substitution `h_k ↦ h′_k h′_{k+1}` maps the
points of the system of `Ω.tieNew p μ k hp hk` to points of `Ω*` in every `F(A)`-group. -/
theorem mapsTo_wordMap_tieNew {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    Set.MapsTo (wordMap ι (Ω.splitWord k)) (V ι (Ω.tieNew p μ k hp hk).toSystem)
      (V ι Ω.toSystem) := fun _ hv =>
  ((mem_V_tieNew_iff hp hk hk' ι).1 hv).1

include hk' in
/-- **ET5, second kind, on group solutions.** Every point of `Ω*` in an `F(A)`-group is the
image under `h_k ↦ h′_k h′_{k+1}` of exactly one point of the system of `Ω.tieNew p μ k hp hk`:
the new boundary connection determines `h′_k`. -/
theorem bijOn_wordMap_tieNew {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    Set.BijOn (wordMap ι (Ω.splitWord k)) (V ι (Ω.tieNew p μ k hp hk).toSystem)
      (V ι Ω.toSystem) :=
  Set.InvOn.bijOn ⟨fun _ hv => wordMap_tieWord_wordMap_splitWord hp hk hk' ι hv,
    fun v _ => wordMap_splitWord_wordMap_tieWord ι v⟩ (mapsTo_wordMap_tieNew hp hk hk' ι)
    (mapsTo_wordMap_tieWord hp hk hk' ι)

/-- **ET5, second kind.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by
`h_k ↦ h′_k h′_{k+1}`, where `Ω′ = Ω.tieNew p μ k hp hk`. -/
def tieNewHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.tieNew p μ k hp hk).toSystem) :=
  CoordGroup.homOfMapsToWordMap _ _ _ _ (mapsTo_wordMap_tieNew hp hk hk' _)

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET5 sends the item `h_j` to the image of `h_j`
under `h_k ↦ h′_k h′_{k+1}`. -/
theorem tieNewHom_inr_of (j : Fin Ω.numItems) :
    tieNewHom hp hk hk' ((inr (FreeGroup.of j) : GX (FreeGroup A) (Fin Ω.numItems)) :
      Ω.coordGroup) = (Ω.splitWord k j : (Ω.tieNew p μ k hp hk).coordGroup) := by
  rw [tieNewHom, CoordGroup.homOfMapsToWordMap_mk, eval_inr_of]

/-- **ET5, second kind.** The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` is an isomorphism. -/
theorem tieNewHom_bijective : Function.Bijective (tieNewHom hp hk hk') := by
  -- The inverse is induced by `tieWord`.
  let ψ : GHom (CoordGroup.coeff (.id (FreeGroup A)) (Ω.tieNew p μ k hp hk).toSystem)
      (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem) :=
    CoordGroup.homOfMapsToWordMap _ _ _ _ (mapsTo_wordMap_tieWord hp hk hk' _)
  have h₁ : ψ.comp (tieNewHom hp hk hk') = GHom.id _ :=
    CoordGroup.gHom_ext fun j => by
      rw [GHom.coe_comp, Function.comp_apply, tieNewHom_inr_of, CoordGroup.homOfMapsToWordMap_mk,
        eval_tieWord_splitWord, GHom.coe_id, id]
  have h₂ : (tieNewHom hp hk hk').comp ψ = GHom.id _ :=
    CoordGroup.gHom_ext fun x => by
      rw [GHom.coe_comp, Function.comp_apply, CoordGroup.homOfMapsToWordMap_mk, tieNewHom,
        CoordGroup.homOfMapsToWordMap_mk, GHom.coe_id, id, QuotientGroup.eq, mem_Rad]
      intro v hv
      rw [map_mul, map_inv, ← MonoidHom.comp_apply, eval_comp_eval, eval_inr_of,
        ← wordMap_apply, wordMap_tieWord_wordMap_splitWord hp hk hk' _ hv, eval_inr_of,
        inv_mul_cancel]
  exact Function.bijective_iff_has_inverse.2 ⟨ψ, fun x => by simpa using DFunLike.congr_fun h₁ x,
    fun x => by simpa using DFunLike.congr_fun h₂ x⟩

include hk' in
/-- The image under `h_k ↦ h′_k h′_{k+1}` of an equation of `Ω` is an equation of
`Ω.tieNew p μ k hp hk`. -/
private theorem map_mem_equations_tieNew
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)}
    (he : e ∈ Ω.equations) :
    Prod.map (Ω.splitList k) (Ω.splitList k) e ∈ (Ω.tieNew p μ k hp hk).equations :=
  equations_subset_addConnection _ _ (by rw [equations_splitItem hk']; exact ⟨e, he, rfl⟩)

/-- Under a solution of `Ω.tieNew p μ k hp hk`, the two new items spell `h′_k h′_{k+1}`. -/
private theorem substituteVars_segment_tieNew (U : (Ω.tieNew p μ k hp hk).Solution) :
    substituteVars U.word ((Ω.tieNew p μ k hp hk).segment k (k + 2) true) =
      U.word k.castSucc ++ U.word k.succ := by
  have h₁ := (Ω.splitItem k).segment_succ k.castSucc true
  have h₂ := (Ω.splitItem k).segment_succ k.succ true
  simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
  rw [segment_addConnection, ← (Ω.splitItem k).segment_append (Nat.le_add_right (k : ℕ) 1)
    (Nat.le_add_right _ 1), FreeGroup.substituteVars_append, h₁, h₂,
    FreeGroup.substituteVars_singleton_inl, FreeGroup.substituteVars_singleton_inl]

namespace Solution

/-- A solution of `Ω.tieNew p μ k hp hk`, for an item `h_k` without constant base, gives a
solution of `Ω`: the item `h_k` gets the concatenation of the words of the two new items, and
every other item keeps its word. -/
def ofTieNew (U : (Ω.tieNew p μ k hp hk).Solution) : Ω.Solution where
  word := Fin.contractNth k.castSucc (· ++ ·) U.word
  isReduced_word j := by
    rcases eq_or_ne j k with h | h
    · rw [h, Fin.contractNth_apply_of_eq _ _ _ _ rfl, ← substituteVars_segment_tieNew hp hk U]
      -- `h′_k` and `h′_{k+1}` both lie in `Δ(μ)`.
      have h₁ := (Ω.splitItem k).mem_baseItems.1
        (mem_baseItems_splitItem (x := k.castSucc).2 (by simpa using hk))
      have h₂ := (Ω.splitItem k).mem_baseItems.1
        (mem_baseItems_splitItem (x := k.succ).2 (by simpa using hk))
      exact U.isReduced_substituteVars_segment_of_le (Ω.dual μ) h₁.1 h₂.2
    · rw [Fin.contractNth_apply_of_ne k.castSucc _ _ j (Fin.val_ne_of_ne h).symm]
      exact U.isReduced_word _
  word_ne_nil j := by
    rcases eq_or_ne j k with h | h
    · rw [h, Fin.contractNth_apply_of_eq _ _ _ _ rfl]
      exact List.append_ne_nil_of_left_ne_nil (U.word_ne_nil _) _
    · rw [Fin.contractNth_apply_of_ne k.castSucc _ _ j (Fin.val_ne_of_ne h).symm]
      exact U.word_ne_nil _
  isReduced_subst e he := by
    have h := U.isReduced_subst _ (map_mem_equations_tieNew hp hk hk' he)
    rwa [Prod.map_fst, Prod.map_snd, substituteVars_splitList, substituteVars_splitList] at h
  subst_eq e he := by
    have h := U.subst_eq _ (map_mem_equations_tieNew hp hk hk' he)
    rwa [Prod.map_fst, Prod.map_snd, substituteVars_splitList, substituteVars_splitList] at h

/-- The solution of `Ω` given by a solution of `Ω.tieNew p μ k hp hk` assigns to `h_k` the
concatenation of the words of `h′_k` and `h′_{k+1}`, and to every other item the word of the item
with its new number. -/
@[simp]
theorem ofTieNew_word (U : (Ω.tieNew p μ k hp hk).Solution) (j : Fin Ω.numItems) :
    (U.ofTieNew hp hk hk').word j = Fin.contractNth k.castSucc (· ++ ·) U.word j :=
  (rfl)

/-- A boundary of `Ω` sits in the words of the solution given by a solution `U` of
`Ω.tieNew p μ k hp hk` at the position of its renumbered boundary in the words of `U`. -/
theorem prefixLength_ofTieNew (U : (Ω.tieNew p μ k hp hk).Solution) (i : Fin (Ω.numItems + 1)) :
    (U.ofTieNew hp hk hk').prefixLength i = U.prefixLength (k.succ.castSucc.succAbove i) := by
  -- `U` read as a solution of `Ω.splitItem k` has the same words, hence the same prefix lengths.
  rw [← (U.ofAddConnection _ _).prefixLength_succAbove_of_word_eq (U.ofTieNew hp hk hk') rfl i,
    prefixLength_def, prefixLength_def, ofAddConnection_word]

end Solution

/-- The solution of `Ω` given by a solution of `Ω.tieNew p μ k hp hk` is its composite with
`F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem toHom_comp_tieNewHom (U : (Ω.tieNew p μ k hp hk).Solution) :
    U.toHom.comp (tieNewHom hp hk hk') = (U.ofTieNew hp hk hk').toHom := by
  refine CoordGroup.gHom_ext fun j => ?_
  rw [GHom.coe_comp, Function.comp_apply, tieNewHom_inr_of, Solution.toHom_mk,
    Solution.toHom_inr_of, Solution.ofTieNew_word, eval_splitWord]
  -- `FreeGroup.mk` commutes with contracting the words of `h′_k` and `h′_{k+1}`.
  simpa [Function.comp_def, ← Solution.point_apply] using (congr_fun (Fin.comp_contractNth
    (· ++ ·) (· * ·) (fun _ _ => FreeGroup.mul_mk.symm) k.castSucc U.word) j).symm

include hp hk hk' in
/-- A solution of `Ω` whose word of `h_k` has its `d`-th letter at the position of `p` in `μ`,
read in `Δ(μ)`, comes from a solution of `Ω.tieNew p μ k hp hk`. -/
private theorem exists_solution_tieNew_of_eq (U : Ω.Solution) {d : ℕ} (hd₀ : 0 < d)
    (hd : d < (U.word k).length) (h : U.prefixLength p - U.prefixLength (Ω.left μ) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then
        U.prefixLength k + d - U.prefixLength (Ω.left (Ω.dual μ))
      else U.prefixLength (Ω.right (Ω.dual μ)) - (U.prefixLength k + d)) :
    ∃ U' : (Ω.tieNew p μ k hp hk).Solution, U'.ofTieNew hp hk hk' = U := by
  have e := (U.splitItem hd₀ hd).prefixLength_succAbove_of_word_eq U
    (U.contractNth_splitItem_word hd₀ hd).symm
  have key : (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc.succAbove p) -
      (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc.succAbove (Ω.left μ)) =
      if Ω.sign μ = Ω.sign (Ω.dual μ) then
        (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc : ℕ) -
          (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc.succAbove (Ω.left (Ω.dual μ)))
      else (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc.succAbove (Ω.right (Ω.dual μ))) -
        (U.splitItem hd₀ hd).prefixLength (k.succ.castSucc : ℕ) := by
    rw [e, e, e, e, Fin.val_castSucc, Fin.val_succ, Solution.prefixLength_splitItem_add_one]
    exact h
  obtain ⟨U', hU'⟩ := (exists_solution_addConnection_iff _ _ _).2 key
  refine ⟨U', Solution.ext (funext fun j => ?_)⟩
  rw [Solution.ofTieNew_word, hU']
  exact congrFun (U.contractNth_splitItem_word hd₀ hd) j

/-- Under a solution of `Ω.tieNew p μ k hp hk`, the new boundary sits strictly after the
boundary `k` of the corresponding solution of `Ω`. -/
private theorem prefixLength_ofTieNew_lt (U : (Ω.tieNew p μ k hp hk).Solution) :
    (U.ofTieNew hp hk hk').prefixLength k < U.prefixLength (k + 1) := by
  have e := Solution.prefixLength_ofTieNew hp hk hk' U k.castSucc
  rw [(by simp : (k.succ.castSucc.succAbove k.castSucc : ℕ) = k), Fin.val_castSucc] at e
  exact e ▸ U.prefixLength_lt (Nat.lt_add_one _) (by simp)

/-- Under a solution of `Ω.tieNew p μ k hp hk`, the new boundary sits strictly before the
boundary `k + 1` of the corresponding solution of `Ω`. -/
private theorem lt_prefixLength_ofTieNew (U : (Ω.tieNew p μ k hp hk).Solution) :
    U.prefixLength (k + 1) < (U.ofTieNew hp hk hk').prefixLength (k + 1) := by
  have e := Solution.prefixLength_ofTieNew hp hk hk' U k.succ
  simp only [Fin.succAbove_castSucc_self, Fin.val_succ] at e
  exact e ▸ U.prefixLength_lt (Nat.lt_add_one _) (by simp; lia)

/-- The boundary equation of the new connection, under a solution of `Ω.tieNew p μ k hp hk`, as
an identity between prefix lengths of the corresponding solution of `Ω` and of the new
boundary. -/
private theorem prefixLength_ofTieNew_boundary (U : (Ω.tieNew p μ k hp hk).Solution) :
    if Ω.sign μ = Ω.sign (Ω.dual μ) then
      (U.ofTieNew hp hk hk').prefixLength p +
          (U.ofTieNew hp hk hk').prefixLength (Ω.left (Ω.dual μ)) =
        U.prefixLength (k + 1) + (U.ofTieNew hp hk hk').prefixLength (Ω.left μ)
    else (U.ofTieNew hp hk hk').prefixLength p + U.prefixLength (k + 1) =
        (U.ofTieNew hp hk hk').prefixLength (Ω.right (Ω.dual μ)) +
          (U.ofTieNew hp hk hk').prefixLength (Ω.left μ) := by
  simp only [Solution.prefixLength_ofTieNew]
  exact U.prefixLength_boundary ((mem_connections_addConnection _ _).2 (Or.inr (Or.inl rfl)))

/-- A solution of `Ω` comes from a solution of `Ω.tieNew p μ k hp hk` exactly when the position
of the boundary `p` in the word of `μ` lies strictly inside the word of the item `h_k` of
`Δ(μ)`, counted from the left end of `Δ(μ)` when `ε(μ) = ε(Δμ)` and from its right end
otherwise. -/
theorem exists_solution_tieNew_iff (U : Ω.Solution) :
    (∃ U' : (Ω.tieNew p μ k hp hk).Solution, U'.ofTieNew hp hk hk' = U) ↔
      if Ω.sign μ = Ω.sign (Ω.dual μ) then
        U.prefixLength k - U.prefixLength (Ω.left (Ω.dual μ)) <
            U.prefixLength p - U.prefixLength (Ω.left μ) ∧
          U.prefixLength p - U.prefixLength (Ω.left μ) <
            U.prefixLength (k + 1) - U.prefixLength (Ω.left (Ω.dual μ))
      else
        U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength (k + 1) <
            U.prefixLength p - U.prefixLength (Ω.left μ) ∧
          U.prefixLength p - U.prefixLength (Ω.left μ) <
            U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength k := by
  obtain ⟨hk₁, hk₂⟩ := Ω.mem_baseItems.1 hk
  have m₁ := U.prefixLength_mono (Fin.le_def.1 (Ω.crosses_iff.1 hp).1.le)
  have m₂ := U.prefixLength_mono hk₁
  have m₃ := U.prefixLength_mono (Nat.add_one_le_iff.2 hk₂)
  -- The word of `h_k` spans the positions from `P(k)` to `P(k + 1)`.
  have hlen := U.length_substituteVars_segment_add_prefixLength true (Nat.le_add_right (k : ℕ) 1)
  rw [Ω.segment_succ k true, FreeGroup.substituteVars_singleton_inl] at hlen
  constructor
  · rintro ⟨U', rfl⟩
    have := prefixLength_ofTieNew_lt hp hk hk' U'
    have := lt_prefixLength_ofTieNew hp hk hk' U'
    have hb := prefixLength_ofTieNew_boundary hp hk hk' U'
    split_ifs at hb ⊢ <;> lia
  · intro h
    split_ifs at h with hs
    · refine exists_solution_tieNew_of_eq hp hk hk' U (d := U.prefixLength p -
        U.prefixLength (Ω.left μ) - (U.prefixLength k - U.prefixLength (Ω.left (Ω.dual μ))))
        (by lia) (by lia) ?_
      simp only [hs, ↓reduceIte]
      lia
    · refine exists_solution_tieNew_of_eq hp hk hk' U (d := U.prefixLength (Ω.right (Ω.dual μ)) -
        U.prefixLength k - (U.prefixLength p - U.prefixLength (Ω.left μ))) (by lia) (by lia) ?_
      simp only [hs, ↓reduceIte]
      lia

end TieNew

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

/-- A solution of `h₀h₁ = h₂h₃`: `h₀ = ab`, `h₁ = a`, `h₂ = a`, `h₃ = ba`, with `a = 0` and
`b = 1`. Both sides become the reduced word `aba`. -/
private def pairSolution : pairExample.Solution where
  word := ![[(0, true), (1, true)], [(0, true)], [(0, true)], [(1, true), (0, true)]]
  isReduced_word := by unfold FreeGroup.IsReduced; decide
  word_ne_nil := by decide
  isReduced_subst := (forall_mem_equations _).2 ⟨by
    simp only [basicEquation_fst, basicEquation_snd, segment_true]
    unfold FreeGroup.IsReduced
    decide, fun _ hb => absurd hb (Finset.notMem_empty _),
    fun _ hc => absurd hc (Finset.notMem_empty _)⟩
  subst_eq := (forall_mem_equations _).2 ⟨by
    simp only [basicEquation_fst, basicEquation_snd, segment_true]
    decide, fun _ hb => absurd hb (Finset.notMem_empty _),
    fun _ hc => absurd hc (Finset.notMem_empty _)⟩

/-- No item of `h₀h₁ = h₂h₃` carries a constant base. -/
private theorem pairExample_not_isConstantItem (k : Fin 4) : ¬ pairExample.IsConstantItem k :=
  fun h => by
    obtain ⟨b, hb, -⟩ := pairExample.isConstantItem_iff.1 h
    exact Finset.notMem_empty b hb

/-- ET5 of the second kind ties the boundary `p = 1` of `μ = [0, 2]` in `h₀h₁ = h₂h₃` to a new
boundary splitting an item of `Δ(μ) = [2, 4]`. Under the solution `(ab, a, a, ba)` the boundary
`p` lies after two letters of the word `aba` of `μ`, that is, strictly inside the word `ba` of
`h₃` read in `Δ(μ)`: the solution comes from the equation with `h₃` split, and not from the
equation with `h₂` split. -/
example : (∃ U' : (pairExample.tieNew 1 0 3 (by decide)
      (pairExample.mem_baseItems.2 ⟨by decide, by decide⟩)).Solution,
        U'.ofTieNew _ _ (pairExample_not_isConstantItem 3) = pairSolution) ∧
    ¬ ∃ U' : (pairExample.tieNew 1 0 2 (by decide)
      (pairExample.mem_baseItems.2 ⟨by decide, by decide⟩)).Solution,
        U'.ofTieNew _ _ (pairExample_not_isConstantItem 2) = pairSolution := by
  rw [exists_solution_tieNew_iff, exists_solution_tieNew_iff]
  simp only [Solution.prefixLength_def]
  decide

end GenEq

end TauCeti
