/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Nat.Pairing
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Merzljakov.Block.InsertAll

/-!
# Merzljakov's theorem for one block of quantifiers, and the values of the formal solution

Let `w` be an element of `FreeGroup ((X ⊕ Y) ⊕ A)`, viewed as the left-hand side of an equation
`w(x, y) = 1` with constants in `FreeGroup A`, universally quantified variables
`x = Sum.inl (Sum.inl i)` and existentially quantified variables `y = Sum.inl (Sum.inr j)`, all of
them after the universal ones. Suppose that `f` chooses witnesses: `w(x, f x) = 1` holds in
`FreeGroup A` for all `x`. If `A` has two distinct letters, the equation has a formal solution:
words `y j ∈ FreeGroup (X ⊕ A)` such that `w(x, y) = 1` holds in `FreeGroup (X ⊕ A)`. Moreover,
the formal solution takes, at some point `g : X → FreeGroup A`, the values of the chosen
witnesses: `y j (g) = f g j`.

The last property is what turns Merzljakov's theorem into its form with an inequation: if the
witnesses `f x` also satisfy `u(x, f x) ≠ 1`, then `u(x, y) ≠ 1` in `FreeGroup (X ⊕ A)`, since its
specialisation at `g` is `u(g, f g) ≠ 1`.

## Proof outline

Represent `w` by a word `W` of length `L` and give each variable `x` occurring in `W` a list of
`L² + 1` exponents, the lists of distinct variables being disjoint; `g x` is the Merzljakov word
with these exponents. Substituting `g` and the witnesses `f g` into `W` gives the identity of
`FreeGroup A`. Inserting each `x` into a block `b a^{m x} b` of `g x` that no factorisation into
cancellation pieces splits keeps the identity (`FreeGroup.exists_lift_mk_blockInsertAll_eq_one`)
and turns `g x = u x * v x` into `u x * x * v x`
(`FreeGroup.exists_mk_blockInsertAll_merzljakovWord`). The endomorphism `x ↦ (u x)⁻¹ x (v x)⁻¹`
then gives the formal solution (`FreeGroup.lift_eq_one_of_translate`), and erasing the variables
shows that its values at `g` are the witnesses `f g`.

## Implementation notes

The construction is that of the proof of Merzljakov's theorem for alternating blocks of
quantifiers, `FreeGroup.exists_formalSolution_of_skolem` in
`TauCeti.GroupTheory.FreeGroup.Merzljakov.FormalSolution`, whose shared steps are in
`TauCeti.GroupTheory.FreeGroup.Merzljakov.Block.InsertAll`, specialised to one block of quantifiers
and extended by the values at the point `g`. With one block, the Merzljakov words only need
disjoint exponent lists, with no condition on the witnesses, and only the variables occurring in
`w` are inserted, so `X` and `Y` may be infinite.

## Main results

* `FreeGroup.exists_formalSolution_lift_eq_of_skolem`: a formal solution of `w(x, y) = 1` whose
  values at one point are the chosen witnesses.

## References

* Yu. I. Merzljakov, *Positive formulae on free groups*, Algebra i Logika 5 (1966), 25–42.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.4, Merzljakov's Theorem and the proof of Theorem 4.
-/

public section

namespace FreeGroup

open List

/-- For every list `l` of variables there are nodup exponent lists of a given length, one for each
variable, such that the list of a variable of `l` is disjoint from the lists of the others. -/
private theorem exists_exponentLists {X : Type*} (l : List X) (N : ℕ) : ∃ ms : X → List ℕ,
    (∀ x, (ms x).Nodup ∧ (ms x).length = N) ∧ ∀ x ∈ l, ∀ x', ∀ n ∈ ms x, n ∈ ms x' → x = x' := by
  classical
  refine ⟨fun x ↦ (range N).map (Nat.pair (l.idxOf x)), fun x ↦ ⟨nodup_range.map fun _ _ h ↦
    (Nat.pair_eq_pair.1 h).2, by simp⟩, fun x hx x' n h h' ↦ ?_⟩
  obtain ⟨r, -, rfl⟩ := mem_map.1 h
  obtain ⟨r', -, hr'⟩ := mem_map.1 h'
  exact (idxOf_inj hx).1 (Nat.pair_eq_pair.1 hr').1.symm

/-- Composing a solution `(x₀, y₀)` in which each `x₀ x` is a two-sided translate `u x * x * v x`
of `x` by constants with the endomorphism `x ↦ (u x)⁻¹ * x * (v x)⁻¹` gives a formal solution,
whose values at the point `x ↦ u x * v x` are the values of `y₀` with the variables erased. -/
private theorem exists_formalSolution_of_mul {A X Y : Type*} (w : FreeGroup ((X ⊕ Y) ⊕ A))
    {y₀ : Y → FreeGroup (X ⊕ A)} {u v : X → FreeGroup A}
    (hw : lift (Sum.elim (Sum.elim (fun x ↦ map Sum.inr (u x) * of (Sum.inl x) * map Sum.inr (v x))
      y₀) (of ∘ Sum.inr)) w = 1) :
    ∃ y : Y → FreeGroup (X ⊕ A), lift (Sum.elim (Sum.elim (of ∘ Sum.inl) y) (of ∘ Sum.inr)) w = 1 ∧
      ∀ j, lift (Sum.elim (fun x ↦ u x * v x) of) (y j) = lift (Sum.elim 1 of) (y₀ j) := by
  let ψ : FreeGroup (X ⊕ A) →* FreeGroup (X ⊕ A) :=
    lift (Sum.elim (fun x ↦ (map Sum.inr (u x))⁻¹ * of (Sum.inl x) * (map Sum.inr (v x))⁻¹)
      (of ∘ Sum.inr))
  refine ⟨fun j ↦ ψ (y₀ j), lift_eq_one_of_translate w hw, fun j ↦ ?_⟩
  have hcomp : (lift (Sum.elim (fun x ↦ u x * v x) of)).comp ψ = lift (Sum.elim 1 of) :=
    ext_hom _ _ fun z ↦ by rcases z with x | c <;> simp [ψ, Function.comp_def]
  exact DFunLike.congr_fun hcomp (y₀ j)

/-- **Merzljakov's theorem** for one block of quantifiers `∀ x ∃ y`, with the values of the formal
solution: if `a ≠ b` are letters of `A` and `w(x, f x) = 1` holds in `FreeGroup A` for all `x`,
then `w(x, y) = 1` has a solution `y` in `FreeGroup (X ⊕ A)` whose values at some point `g` are
the witnesses `f g`. -/
theorem exists_formalSolution_lift_eq_of_skolem {A X Y : Type*} {a b : A} (hab : a ≠ b)
    (w : FreeGroup ((X ⊕ Y) ⊕ A)) (f : (X → FreeGroup A) → Y → FreeGroup A)
    (hw : ∀ x, lift (Sum.elim (Sum.elim x (f x)) of) w = 1) :
    ∃ (y : Y → FreeGroup (X ⊕ A)) (g : X → FreeGroup A),
      lift (Sum.elim (Sum.elim (of ∘ Sum.inl) y) (of ∘ Sum.inr)) w = 1 ∧
        ∀ j, lift (Sum.elim g of) (y j) = f g j := by
  classical
  obtain ⟨W, rfl⟩ : ∃ W, mk W = w := ⟨w.toWord, mk_toWord⟩
  -- the variables `x` occurring in `W`, and for each `x` a list of `|W|² + 1` exponents, the
  -- list of a variable of `W` being disjoint from the others
  let xs : List X := (W.filterMap fun c ↦ c.1.getLeft?.bind Sum.getLeft?).dedup
  obtain ⟨ms, hms, hdisj⟩ := exists_exponentLists xs (W.length * W.length + 1)
  -- substitute the Merzljakov words `g x` and the witnesses `f g`, and insert the variables
  let g (x : X) : FreeGroup A := mk (merzljakovWord a b (ms x))
  let U : (X ⊕ Y) ⊕ A → List (A × Bool) :=
    Sum.elim (Sum.elim (fun x ↦ merzljakovWord a b (ms x)) fun j ↦ (f g j).toWord)
      fun c ↦ [(c, true)]
  have hU : (fun z ↦ mk (U z)) = Sum.elim (Sum.elim g (f g)) of := by
    ext ((x | j) | c) <;> simp [U, g, of, mk_toWord]
  obtain ⟨m, hm, hU'⟩ := exists_lift_mk_blockInsertAll_eq_one hab (U := U)
    (fun ⟨z, _⟩ _ ↦ by rcases z with (x | j) | c <;> simp [U, isReduced_toWord]) (hU ▸ hw g)
    (fun x ↦ (hms x).1)
    (fun x ↦ by rw [(hms x).2]; lia) xs
  -- the inserted Merzljakov word of `x ∈ xs` is `u x * x * v x`, with `g x = u x * v x`
  choose u v hg hx₀ using exists_mk_blockInsertAll_merzljakovWord hab (fun x ↦ (hms x).1) hm
    fun x hx x' _ ↦ hdisj x hx x'
  obtain ⟨y, hy, hyg⟩ := exists_formalSolution_of_mul (mk W)
    (y₀ := fun j ↦
      mk (blockInsertAll a b m xs ((U (Sum.inl (Sum.inr j))).map (Prod.map Sum.inr id))))
    (by
      rw [← hU', lift_mk, lift_mk]
      refine congrArg _ (map_congr_left fun ⟨z, e⟩ hz ↦ congrArg (fun q ↦ cond e q q⁻¹) ?_)
      rcases z with (x | j) | c
      · exact (hx₀ x (mem_dedup.2 (mem_filterMap.2 ⟨_, hz, rfl⟩))).symm
      · rfl
      · simp [U, of])
  refine ⟨y, fun x ↦ u x * v x, hy, fun j ↦ ?_⟩
  rw [hyg j, map_mk_blockInsertAll _ (by simp)]
  simp only [Prod.map_def, id_eq, ← map.mk, lift_map, Sum.elim_comp_inr, lift_of_eq_id,
    MonoidHom.id_apply, U, Sum.elim_inl, Sum.elim_inr, mk_toWord]
  exact congrArg (f · j) (funext hg)

end FreeGroup
