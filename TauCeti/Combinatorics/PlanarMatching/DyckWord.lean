/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.DyckWord
public import TauCeti.Combinatorics.NoncrossingPartition.PerfectMatching
public import TauCeti.Combinatorics.PlanarMatching.Basic
import TauCeti.Data.List.OfFn

/-!
# Planar matchings as Dyck words

Read the boundary points `0, …, k - 1` of a planar matching `x` from left to right, writing an up
step `U` at each point `a` where an arc opens (`a < x a`) and a down step `D` where an arc closes.
Every arc contributes its `U` before its `D`, so the word has as many `U`s as `D`s and every prefix
has at least as many `U`s as `D`s: it is a Dyck word (Mathlib's `DyckWord`). For planar matchings
this encoding loses nothing. Two planar matchings that open arcs at the same points are equal,
because the arcs of a planar matching are nested: an arc enclosing only arcs on which the two
matchings agree is forced to agree as well, or the second matching would have interleaving arcs.

This gives the Dyck-word model of planar matchings,
`PlanarMatching (2 * n) ≃ {p : DyckWord // p.semilength = n}`, and with it the Catalan count of
planar matchings. In the Temperley–Lieb picture the word records, from left to right along the
cyclic boundary of a diagram, which points are the left feet of their arcs.

## Main definitions

* `TauCeti.PlanarMatching.dyckStep x a`: the step `U` if the arc of `x` at `a` opens at `a`, and
  `D` if it closes there.
* `TauCeti.PlanarMatching.toDyckWord x`: the Dyck word `dyckStep x 0, …, dyckStep x (k - 1)`.
* `TauCeti.PlanarMatching.dyckWordEquiv n`: the equivalence between the planar matchings of
  `2 * n` points and the Dyck words of semilength `n`.

## Main results

* `TauCeti.PlanarMatching.dyckStep_injective`: a planar matching is determined by the points at
  which its arcs open.
* `TauCeti.PlanarMatching.card_planarMatching`: there are `catalan n` planar matchings of `2 * n`
  points.
* `TauCeti.PlanarMatching.toList_toDyckWord_nested`: the fully nested matching is the word
  `Uⁿ Dⁿ`.

## Implementation notes

Injectivity of the encoding is proved directly; bijectivity then follows from the two Catalan
counts already available (`TauCeti.PerfectMatching.card_isNoncrossingMatching_eq_catalan` for
noncrossing matchings, `DyckWord.card_dyckWord_semilength_eq_catalan` for Dyck words). The
inverse of `dyckWordEquiv` is the computable search `Fintype.bijInv`.

## References

* R. P. Stanley, *Catalan Numbers*, Cambridge University Press, 2015, Chapter 2.
-/

public section

open DyckStep Finset

namespace TauCeti.PlanarMatching

variable {k : ℕ}

/-- The **Dyck step** of a planar matching `x` at the boundary point `a`: the up step `U` if the
arc at `a` opens there (`a < x a`), and the down step `D` if it closes there (`x a < a`). -/
def dyckStep (x : PlanarMatching k) (a : Fin k) : DyckStep :=
  if a < x.1.val a then U else D

/-- A planar matching has an up step exactly where an arc opens. -/
@[simp]
theorem dyckStep_eq_U_iff {x : PlanarMatching k} {a : Fin k} :
    x.dyckStep a = U ↔ a < x.1.val a := by
  unfold dyckStep
  split_ifs with h <;> simp [h]

/-- A planar matching has a down step exactly where an arc closes. -/
@[simp]
theorem dyckStep_eq_D_iff {x : PlanarMatching k} {a : Fin k} :
    x.dyckStep a = D ↔ x.1.val a < a := by
  unfold dyckStep
  split_ifs with h
  · simp [h.not_gt]
  · simp [(not_lt.mp h).lt_of_ne (x.1.apply_ne a)]

/-- In every prefix, the arcs closing before `j` inject into the arcs opening before `j`, by
sending a closing point to its partner. -/
private theorem card_closing_le_card_opening (x : PlanarMatching k) (j : ℕ) :
    #{a : Fin k | (a : ℕ) < j ∧ x.dyckStep a = D} ≤
      #{a : Fin k | (a : ℕ) < j ∧ x.dyckStep a = U} := by
  refine card_le_card_of_injOn x.1.val (fun a ha => ?_) x.1.val.injective.injOn
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, dyckStep_eq_U_iff,
    dyckStep_eq_D_iff, x.1.apply_apply] at ha ⊢
  exact ⟨lt_trans (Fin.lt_def.mp ha.2) ha.1, ha.2⟩

/-- Over the whole boundary, the partner map exchanges the closing and the opening points. -/
private theorem card_closing_eq_card_opening (x : PlanarMatching k) :
    #{a : Fin k | (a : ℕ) < k ∧ x.dyckStep a = D} =
      #{a : Fin k | (a : ℕ) < k ∧ x.dyckStep a = U} := by
  refine card_nbij' x.1.val x.1.val (fun a ha => ?_) (fun a ha => ?_)
    (fun a _ => x.1.apply_apply a) (fun a _ => x.1.apply_apply a)
  all_goals
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, dyckStep_eq_U_iff,
      dyckStep_eq_D_iff, x.1.apply_apply, Fin.is_lt] at ha ⊢
    exact ha

/-- The **Dyck word of a planar matching**: the steps `dyckStep x 0, …, dyckStep x (k - 1)`, an up
step where an arc opens and a down step where it closes. -/
def toDyckWord (x : PlanarMatching k) : DyckWord where
  toList := List.ofFn x.dyckStep
  count_U_eq_count_D := by
    rw [← List.take_length (l := List.ofFn x.dyckStep), List.length_ofFn,
      List.count_take_ofFn, List.count_take_ofFn, card_closing_eq_card_opening]
  count_D_le_count_U j := by
    rw [List.count_take_ofFn, List.count_take_ofFn]
    exact card_closing_le_card_opening x j

/-- The letters of the Dyck word of a planar matching are its Dyck steps. -/
@[simp]
theorem toList_toDyckWord (x : PlanarMatching k) :
    x.toDyckWord.toList = List.ofFn x.dyckStep := (rfl)

/-- The Dyck word of a planar matching of `k` points has length `k`, so twice its semilength is
`k`. -/
theorem two_mul_semilength_toDyckWord (x : PlanarMatching k) :
    2 * x.toDyckWord.semilength = k := by
  rw [DyckWord.two_mul_semilength_eq_length, toList_toDyckWord, List.length_ofFn]

/-- The Dyck word of a planar matching of `2 * n` points has semilength `n`. -/
@[simp]
theorem semilength_toDyckWord {n : ℕ} (x : PlanarMatching (2 * n)) :
    x.toDyckWord.semilength = n := by
  have := x.two_mul_semilength_toDyckWord
  omega

/-- Two planar matchings agree at a point `c` once they agree at whichever of `c` and its partner
opens the arc between them. -/
private theorem apply_eq_of_forall_opening {x y : PlanarMatching k} {c : Fin k}
    (h : ∀ b, (b = c ∨ b = x.1.val c) → b < x.1.val b → y.1.val b = x.1.val b) :
    y.1.val c = x.1.val c := by
  rcases lt_or_gt_of_ne (x.1.apply_ne c) with hc | hc
  · -- The arc closes at `c`, so it opens at `x c`, where the two matchings agree.
    have := h _ (.inr rfl) (by rwa [x.1.apply_apply])
    rwa [x.1.apply_apply, y.1.apply_eq_comm] at this
  · exact h c (.inl rfl) hc

/-- If two planar matchings open arcs at the same points and agree strictly inside the arc
`{a, x a}` of `x`, then they agree at `a`: otherwise the arcs of `y` at `a` and at `x a` would
interleave. -/
private theorem apply_eq_of_eqOn_Ioo {x y : PlanarMatching k}
    (h : ∀ a, a < x.1.val a ↔ a < y.1.val a) {a : Fin k} (ha : a < x.1.val a)
    (hin : ∀ c, a < c → c < x.1.val a → y.1.val c = x.1.val c) : y.1.val a = x.1.val a := by
  -- A point inside the arc is not matched by `y` to an endpoint of the arc.
  have hout : ∀ c, a < c → c < x.1.val a → ∀ e, y.1.val e = c → a < e ∧ e < x.1.val a := by
    intro c hac hcb e he
    rw [← y.1.apply_eq_comm, hin c hac hcb] at he
    exact he ▸ x.val_apply_mem_Ioo hac hcb
  by_contra hne
  -- Otherwise `y` matches `a` beyond `x a` and `x a` before `a`, so its two arcs interleave.
  have hya : x.1.val a < y.1.val a := by
    rcases lt_trichotomy (y.1.val a) (x.1.val a) with h' | h' | h'
    · exact absurd (hout _ ((h a).1 ha) h' a rfl).1 (lt_irrefl a)
    · exact absurd h' hne
    · exact h'
  have hyb : y.1.val (x.1.val a) < a := by
    have hb : y.1.val (x.1.val a) < x.1.val a := by
      refine (not_lt.mp fun h' => ?_).lt_of_ne (y.1.apply_ne _)
      exact (lt_asymm ha) (by simpa only [x.1.apply_apply] using (h (x.1.val a)).2 h')
    rcases lt_trichotomy (y.1.val (x.1.val a)) a with h' | h' | h'
    · exact h'
    · exact absurd (y.1.apply_eq_comm.mpr h') hne
    · exact absurd (hout _ h' hb (x.1.val a) rfl).2 (lt_irrefl _)
  exact Equiv.Perm.isNoncrossingMatching_iff.mp y.2 hyb (by rwa [y.1.apply_apply])
    (by rwa [y.1.apply_apply])

/-- **A planar matching is determined by the points at which its arcs open.** -/
theorem dyckStep_injective : Function.Injective (dyckStep (k := k)) := by
  intro x y hxy
  have h : ∀ a, a < x.1.val a ↔ a < y.1.val a := fun a => by
    rw [← dyckStep_eq_U_iff, ← dyckStep_eq_U_iff, hxy]
  -- Every arc of `x` is an arc of `y`, by strong induction on the length of the arc.
  have H : ∀ d (a : Fin k), a < x.1.val a → (x.1.val a : ℕ) - a = d →
      y.1.val a = x.1.val a := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro a ha hd
    -- Inside the arc `{a, x a}` the two matchings agree, by the induction hypothesis: the arcs
    -- there are nested in `{a, x a}`, hence shorter.
    refine apply_eq_of_eqOn_Ioo h ha fun c hac hcb =>
      apply_eq_of_forall_opening fun b hb hb' => ih _ ?_ b hb' rfl
    have hc := x.val_apply_mem_Ioo hac hcb
    rw [Set.mem_Ioo, Fin.lt_def, Fin.lt_def] at hc
    rw [Fin.lt_def] at hac hcb hb'
    rcases hb with rfl | rfl
    · omega
    · rw [x.1.apply_apply] at hb' ⊢
      omega
  exact PlanarMatching.ext fun a => (apply_eq_of_forall_opening fun b _ hb => H _ b hb rfl).symm

/-- **The Dyck word of a planar matching determines it.** -/
theorem toDyckWord_injective : Function.Injective (toDyckWord (k := k)) := fun _ _ h =>
  dyckStep_injective (List.ofFn_injective (congrArg DyckWord.toList h))

/-- Two planar matchings are equal exactly when their Dyck words are. -/
@[simp]
theorem toDyckWord_inj {x y : PlanarMatching k} : x.toDyckWord = y.toDyckWord ↔ x = y :=
  toDyckWord_injective.eq_iff

/-- **The Catalan count.** There are `catalan n` planar matchings of `2 * n` points. -/
theorem card_planarMatching (n : ℕ) : Nat.card (PlanarMatching (2 * n)) = catalan n :=
  PerfectMatching.card_isNoncrossingMatching_eq_catalan (Fintype.card_fin _)

private theorem bijective_toDyckWord (n : ℕ) :
    Function.Bijective fun x : PlanarMatching (2 * n) =>
      (⟨x.toDyckWord, x.semilength_toDyckWord⟩ : {p : DyckWord // p.semilength = n}) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => ?_, ?_⟩
  · exact toDyckWord_injective (congrArg Subtype.val h)
  · rw [DyckWord.card_dyckWord_semilength_eq_catalan, ← Nat.card_eq_fintype_card,
      card_planarMatching]

/-- **The Dyck-word model of planar matchings.** Recording at each boundary point whether its arc
opens or closes there is an equivalence between the planar matchings of `2 * n` points and the
Dyck words of semilength `n`. -/
def dyckWordEquiv (n : ℕ) : PlanarMatching (2 * n) ≃ {p : DyckWord // p.semilength = n} where
  toFun x := ⟨x.toDyckWord, x.semilength_toDyckWord⟩
  invFun := Fintype.bijInv (bijective_toDyckWord n)
  left_inv := Fintype.leftInverse_bijInv (bijective_toDyckWord n)
  right_inv := Fintype.rightInverse_bijInv (bijective_toDyckWord n)

@[simp]
theorem coe_dyckWordEquiv_apply (n : ℕ) (x : PlanarMatching (2 * n)) :
    (dyckWordEquiv n x : DyckWord) = x.toDyckWord := (rfl)

/-- The planar matching of a Dyck word has that Dyck word. -/
@[simp]
theorem toDyckWord_dyckWordEquiv_symm_apply (n : ℕ) (p : {p : DyckWord // p.semilength = n}) :
    ((dyckWordEquiv n).symm p).toDyckWord = p := by
  rw [← coe_dyckWordEquiv_apply, Equiv.apply_symm_apply]

/-- The fully nested planar matching opens its arcs at the first `n` points and closes them at the
last `n`: its Dyck word is `Uⁿ Dⁿ`. -/
theorem toList_toDyckWord_nested (n : ℕ) :
    (nested n).toDyckWord.toList = List.replicate n U ++ List.replicate n D := by
  have h : ∀ a : Fin (n + n), (nested n).dyckStep a = if (a : ℕ) < n then U else D := by
    intro a
    simp only [dyckStep, nested_val, Fin.revPerm_apply, Fin.lt_def, Fin.val_rev]
    split_ifs <;> first | rfl | omega
  have hfun : (nested n).dyckStep = fun a : Fin (n + n) => if (a : ℕ) < n then U else D :=
    funext h
  rw [toList_toDyckWord, hfun, List.ofFn_add]
  simp [List.ofFn_const]

end TauCeti.PlanarMatching
