/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Surgery
import Mathlib.Data.Fin.VecNotation

/-!
# Removal of a pair of matched bases

Two dual variable bases `μ, Δ(μ)` of a generalised equation `Ω` form a *matched pair* when they
start at the same boundary, `α(μ) = α(Δμ)` (Kharlampovich–Myasnikov, Definition 10(3)). The
elementary transformation ET3 (§5.1) removes a matched pair together with the boundary connections
through it. If `Ω` is formally consistent, the bases of a matched pair have the same sign and every
connection through `μ` has the form `(p, μ, p)`; if the two bases also end at the same boundary,
every removed equation has two identical sides. Consequently, writing `Ω′ = Ω.removePair μ`:

* `Ω′` has the same items and is formally consistent
  (`TauCeti.GenEq.IsFormallyConsistent.removeBases`), and `Ω*`, `Ω′*` have the same points in
  every `F(A)`-group (`TauCeti.GenEq.V_toSystem_removePair`);
* the identity on the items induces an `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}`
  (`TauCeti.GenEq.removePairHom`, `TauCeti.GenEq.removePairHom_bijective`);
* every solution `U` of `Ω` is a solution of `Ω′` with the same words, and it is the unique
  solution of `Ω′` whose homomorphism composed with `F_{R(Ω)} → F_{R(Ω′)}` is the homomorphism of
  `U` (`TauCeti.GenEq.toHom_comp_removePairHom_eq_iff`);
* the solutions of `Ω` are exactly the solutions of `Ω′` for which the word `U[α(μ), β(μ)]` is
  reduced as written (`TauCeti.GenEq.solutionEquivRemovePair`).

The source asserts that `β(μ) = β(Δμ)` follows from formal consistency and that `Ω` and `Ω′` have
the same solutions; neither holds in general. Definition 10 does not constrain right end-points,
so `β(μ) = β(Δμ)` is a hypothesis here. A solution of `Ω` must make `U[α(μ), β(μ)]` reduced as
written, which `Ω′` does not require: the examples at the end of the file show a matched pair on
one item, where the solutions do coincide, and a matched pair on two items, where `(a, a⁻¹)` solves
`Ω′` but not `Ω`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), Definition 10 and §5.1, ET3 and the remark after it.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET3.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars substituteVars_append)

variable {A : Type*} {Ω : GenEq A} {μ : Fin Ω.numBases}

section Matched

variable (hΩ : Ω.IsFormallyConsistent) (hl : Ω.left μ = Ω.left (Ω.dual μ))
  (hr : Ω.right μ = Ω.right (Ω.dual μ))

include hl in
/-- The two bases of a matched pair start at the same boundary as `μ`. -/
private theorem left_eq_of_mem_pair {ν : Fin Ω.numBases}
    (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) : Ω.left ν = Ω.left μ := by
  rcases Finset.mem_insert.1 hν with rfl | hν
  · rfl
  · rw [Finset.mem_singleton.1 hν, hl]

include hr in
/-- The two bases of a matched pair end at the same boundary as `μ`. -/
private theorem right_eq_of_mem_pair {ν : Fin Ω.numBases}
    (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) : Ω.right ν = Ω.right μ := by
  rcases Finset.mem_insert.1 hν with rfl | hν
  · rfl
  · rw [Finset.mem_singleton.1 hν, hr]

include hl in
/-- A base of a matched pair starts at the same boundary as its dual. -/
private theorem left_eq_left_dual_of_mem_pair {ν : Fin Ω.numBases}
    (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) : Ω.left ν = Ω.left (Ω.dual ν) := by
  rw [left_eq_of_mem_pair hl hν,
    left_eq_of_mem_pair hl (Ω.dual_mem_pair μ ν hν)]

include hΩ hl hr in
/-- The basic equation of a base of a matched pair has two identical sides. -/
private theorem basicEquation_fst_eq_snd {ν : Fin Ω.numBases}
    (hν : ν ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) :
    (Ω.basicEquation ν).1 = (Ω.basicEquation ν).2 := by
  have hν' := Ω.dual_mem_pair μ ν hν
  simp [left_eq_of_mem_pair hl hν, left_eq_of_mem_pair hl hν', right_eq_of_mem_pair hr hν,
    right_eq_of_mem_pair hr hν', hΩ.sign_eq_of_left_eq (left_eq_left_dual_of_mem_pair hl hν)]

include hΩ hl in
/-- The boundary equation of a connection through a base of a matched pair has two identical
sides: it is `h[α(μ), p] = h[α(μ), p]`. -/
private theorem boundaryEquation_fst_eq_snd
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections)
    (hν : c.2.1 ∈ ({μ, Ω.dual μ} : Finset (Fin Ω.numBases))) :
    (Ω.boundaryEquation c).1 = (Ω.boundaryEquation c).2 := by
  have hleft := left_eq_left_dual_of_mem_pair hl hν
  rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq (hΩ.sign_eq_of_left_eq hleft),
    hleft, hΩ.eq_of_left_eq c hc hleft]

include hΩ hl hr in
/-- **ET3 on group solutions.** Removing a matched pair `μ, Δ(μ)` with `β(μ) = β(Δμ)` from a
formally consistent generalised equation does not change the points of `Ω*` in any
`F(A)`-group. -/
theorem V_toSystem_removePair {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι (Ω.removePair μ).toSystem = V ι Ω.toSystem :=
  (V_toSystem_removeBases_subset _ ι (fun _ hν => basicEquation_fst_eq_snd hΩ hl hr hν)
    fun _ hc hν => boundaryEquation_fst_eq_snd hΩ hl hc hν).antisymm
      (V_toSystem_subset_removeBases _ ι)

/-- **ET3 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
identity on the items, where `Ω` is formally consistent and `Ω′` is `Ω` with a matched pair
`μ, Δ(μ)` with `β(μ) = β(Δμ)` removed. -/
def removePairHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.removePair μ).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_removePair hΩ hl hr _).le

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET3 is the identity on the words in the items. -/
-- Not `@[simp]`: the reducible `removePair` in the codomain keeps `simp` from indexing this lemma
-- uninstantiated, so it is used through `rw`.
theorem removePairHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    removePairHom hΩ hl hr (w : Ω.coordGroup) = (w : (Ω.removePair μ).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- **ET3 on coordinate groups.** If `Ω` is formally consistent, the identity on the items induces
an `F(A)`-isomorphism of the coordinate groups of `Ω` and of `Ω` with a matched pair `μ, Δ(μ)` with
`β(μ) = β(Δμ)` removed. -/
theorem removePairHom_bijective : Function.Bijective (removePairHom hΩ hl hr) :=
  ⟨CoordGroup.homOfVSubset_injective _ (V_toSystem_removePair hΩ hl hr _).ge,
    CoordGroup.homOfVSubset_surjective _⟩

/-- The homomorphism `F_{R(Ω′)} → F(A)` of a solution `U` of `Ω`, viewed as a solution of `Ω′`,
composed with `F_{R(Ω)} → F_{R(Ω′)}` is the homomorphism of `U`. -/
theorem toHom_comp_removePairHom (U : Ω.Solution) :
    (U.removePair μ).toHom.comp (removePairHom hΩ hl hr) = U.toHom := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, removePairHom_mk]
  simp

/-- **ET3 transfers solutions uniquely.** The solution of `Ω` with a matched pair removed that
corresponds to a solution `U` of `Ω` through `F_{R(Ω)} → F_{R(Ω′)}` is `U` itself. -/
theorem toHom_comp_removePairHom_eq_iff (U : Ω.Solution) (U' : (Ω.removePair μ).Solution) :
    U'.toHom.comp (removePairHom hΩ hl hr) = U.toHom ↔ U' = U.removePair μ := by
  refine ⟨fun h => Solution.point_injective (funext fun k => ?_), ?_⟩
  · have h' := DFunLike.congr_fun h ((inr (FreeGroup.of k) : GX (FreeGroup A) _) : Ω.coordGroup)
    rw [GHom.coe_comp, Function.comp_apply, removePairHom_mk, Solution.toHom_inr_of,
      Solution.toHom_inr_of] at h'
    simpa using h'
  · rintro rfl
    exact toHom_comp_removePairHom hΩ hl hr U

/-! ### Solutions -/

include hΩ hl hr in
/-- A solution of `Ω` with a matched pair removed for which `U[α(μ), β(μ)]` is reduced as written
makes every equation of `Ω` reduced as written. -/
private theorem isReduced_subst_of_removePair (U : (Ω.removePair μ).Solution)
    (h : FreeGroup.IsReduced (substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true))) :
    ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars U.word e.1) ∧
      FreeGroup.IsReduced (substituteVars U.word e.2) := by
  intro e he
  rcases equations_subset_union_removeBases _ he with he | ⟨ν, hν, rfl⟩ | ⟨c, ⟨hc, hν⟩, rfl⟩
  · exact U.isReduced_subst e he
  · rw [← basicEquation_fst_eq_snd hΩ hl hr hν, and_self, basicEquation_fst,
      left_eq_of_mem_pair hl hν, right_eq_of_mem_pair hr hν]
    exact (Ω.isReduced_substituteVars_segment_iff _ _ _ _).2 h
  · rw [← boundaryEquation_fst_eq_snd hΩ hl hc hν, and_self, boundaryEquation_fst,
      left_eq_of_mem_pair hl hν]
    obtain ⟨h₁, h₂, -, -⟩ := Ω.bounds_of_mem_connections c hc
    rw [left_eq_of_mem_pair hl hν] at h₁
    rw [right_eq_of_mem_pair hr hν] at h₂
    rw [← Ω.segment_append h₁.le h₂.le (Ω.right μ).is_le, substituteVars_append] at h
    exact h.infix (List.prefix_append _ _).isInfix

include hΩ hl hr in
/-- **ET3 on solutions.** If `Ω` is formally consistent and `μ, Δ(μ)` is a matched pair with
`β(μ) = β(Δμ)`, the solutions of `Ω` are the solutions of `Ω` with that pair removed for which the
word `U[α(μ), β(μ)]` is reduced as written. The words of the items are unchanged. -/
def solutionEquivRemovePair : Ω.Solution ≃ {U : (Ω.removePair μ).Solution //
    FreeGroup.IsReduced (substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true))} where
  toFun U := ⟨U.removePair μ, by
    rw [Solution.removeBases_word]
    exact U.isReduced_substituteVars_segment μ⟩
  invFun U := Solution.ofMemV U.1.word U.1.isReduced_word U.1.word_ne_nil
    (isReduced_subst_of_removePair hΩ hl hr U.1 U.2)
    (funext U.1.point_apply ▸ (V_toSystem_removePair hΩ hl hr _).le U.1.point_mem_V)
  left_inv U := Solution.ext ((Solution.ofMemV_word ..).trans (U.removeBases_word _))
  right_inv U := Subtype.ext (Solution.ext ((Solution.removeBases_word _ _).trans
    (Solution.ofMemV_word ..)))

/-- ET3 sends a solution `U` of `Ω` to `U` viewed as a solution of `Ω` with the pair removed. -/
@[simp]
theorem solutionEquivRemovePair_apply_coe (U : Ω.Solution) :
    (solutionEquivRemovePair hΩ hl hr U : (Ω.removePair μ).Solution) = U.removePair μ :=
  (rfl)

variable (U : {U : (Ω.removePair μ).Solution //
  FreeGroup.IsReduced (substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true))})

/-- The inverse of ET3 on solutions keeps the words of the items. -/
@[simp]
theorem solutionEquivRemovePair_symm_apply_word :
    ((solutionEquivRemovePair hΩ hl hr).symm U).word = U.1.word :=
  Solution.ofMemV_word ..

/-- The inverse of ET3 on solutions keeps the point of a solution. -/
@[simp]
theorem solutionEquivRemovePair_symm_apply_point :
    ((solutionEquivRemovePair hΩ hl hr).symm U).point = U.1.point := by
  ext
  simp

/-- The inverse of ET3 on solutions keeps the positions of the boundaries. -/
@[simp]
theorem solutionEquivRemovePair_symm_apply_prefixLength :
    ((solutionEquivRemovePair hΩ hl hr).symm U).prefixLength = U.1.prefixLength := by
  ext
  simp [Solution.prefixLength_def]

/-- The homomorphism `F_{R(Ω)} → F(A)` of the solution of `Ω` corresponding to a solution `U` of `Ω`
with a matched pair removed is that of `U` composed with `F_{R(Ω)} → F_{R(Ω′)}`. -/
theorem solutionEquivRemovePair_symm_apply_toHom :
    ((solutionEquivRemovePair hΩ hl hr).symm U).toHom =
      U.1.toHom.comp (removePairHom hΩ hl hr) := by
  conv_rhs => rw [← (solutionEquivRemovePair hΩ hl hr).apply_symm_apply U]
  exact (toHom_comp_removePairHom hΩ hl hr _).symm

end Matched

/-! ### Examples -/

/-- The generalised equation with `n` items covered by a matched pair of bases, both spanning
`h₁ ⋯ hₙ`: its basic equations are `h₁ ⋯ hₙ = h₁ ⋯ hₙ`. -/
private abbrev matched (n : ℕ) (hn : 0 < n) : GenEq (Fin 2) where
  numItems := n
  numBases := 2
  left _ := 0
  right _ := Fin.last n
  left_lt_right _ := by simpa [Fin.lt_def] using hn
  sign _ := true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- Removing the matched pair of `matched n` leaves no variable bases. -/
private theorem numBases_matched_removePair (n : ℕ) (hn : 0 < n) :
    ((matched n hn).removePair 0).numBases = 0 :=
  numBases_removePair (μ := 0) (by simp)

/-- Removing the matched pair covering a single item imposes no new condition on that item and
loses no solution: every nonempty reduced word `w` is the word of `h₁` in a solution of
`matched 1`, as it is in a solution of the result. -/
example (w : List (Fin 2 × Bool)) (hw : FreeGroup.IsReduced w) (hw' : w ≠ []) :
    ∃ U : (matched 1 one_pos).Solution, U.word 0 = w := by
  let U' := Solution.ofNumBasesEqZero (numBases_matched_removePair 1 one_pos) rfl (fun _ => w)
    (fun _ => hw) fun _ => hw'
  have hseg : (matched 1 one_pos).segment ((matched 1 one_pos).left 0)
      ((matched 1 one_pos).right 0) true = [(Sum.inl 0, true)] := by
    rw [segment_true]
    decide
  refine ⟨(solutionEquivRemovePair (μ := 0)
    (isFormallyConsistent_of_sign_eq (fun _ => rfl) rfl rfl) rfl rfl).symm ⟨U', ?_⟩, by simp [U']⟩
  rw [hseg]
  simpa [U'] using hw

/-- Removing a matched pair can lose the condition that the word of its segment is reduced as
written: `h₁ = a`, `h₂ = a⁻¹` (with `a = 0`) is a solution of `matched 2` with the matched pair
removed, but not of `matched 2`, as `a a⁻¹` is not reduced. -/
example : ∃ U' : ((matched 2 two_pos).removePair 0).Solution,
    ∀ U : (matched 2 two_pos).Solution, U.word ≠ U'.word := by
  refine ⟨Solution.ofNumBasesEqZero (numBases_matched_removePair 2 two_pos) rfl
    ![[(0, true)], [(0, false)]] (by unfold FreeGroup.IsReduced; decide) (by decide), ?_⟩
  intro U hU
  have h := U.isReduced_substituteVars_segment 0
  rw [segment_true, hU, Solution.ofNumBasesEqZero_word] at h
  revert h
  unfold FreeGroup.IsReduced
  decide

end GenEq

end TauCeti
