/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Basic
import TauCeti.Order.Interval.Set.Fin

/-!
# Juxtaposing, nesting, contracting and gluing planar matchings

Operations on planar matchings, out of which `TauCeti.TLDiagram.comp` composes Temperley–Lieb
diagrams and `TauCeti.TLDiagram.tensor` juxtaposes them.

* **Juxtaposition** `TauCeti.PlanarMatching.append x y` places the arcs of `y` after those of `x`.
* **Nesting** `TauCeti.PlanarMatching.nest x y` inserts the arcs of a planar matching `y` of `l`
  points between the first `k` and the last `r` points of a planar matching `x` of `k + r` points.
  The result is planar because no arc of `x` separates the inserted block of consecutive points.
* **Contraction** `TauCeti.PlanarMatching.contract x a` joins the two consecutive points `a` and
  `a + 1` by a small arc outside the disc and deletes them from the boundary: the partners of `a`
  and of `a + 1` become partners of each other. If `a` and `a + 1` were partners already, the
  small arc and the arc of `x` close up into a circle. The result is again a planar matching,
  because the new arc runs along the two old ones, across the gap between `a` and `a + 1`.
* **Gluing across the middle** `TauCeti.PlanarMatching.glueMiddle m` contracts the `m` nested
  pairs of consecutive points around the middle of a planar matching of `n + m + (m + p)` points,
  innermost first, and `TauCeti.PlanarMatching.glueMiddleCircles m` counts the circles closed on
  the way. Next to a fully nested block, each contraction pulls a strand straight.

## Main definitions

* `TauCeti.PlanarMatching.append`: juxtaposition of planar matchings.
* `TauCeti.PlanarMatching.nest`: nesting a planar matching into another one.
* `TauCeti.PlanarMatching.contract`: joining two consecutive boundary points.
* `TauCeti.PlanarMatching.glueMiddle`, `TauCeti.PlanarMatching.glueMiddleCircles`: contracting `m`
  nested pairs of consecutive points around the middle, and the number of circles this closes.

## Main results

* `TauCeti.PlanarMatching.succAbove_succAbove_contract_val`: the partner of a point after
  contraction.
* `TauCeti.PlanarMatching.glueMiddle_append_nested`,
  `TauCeti.PlanarMatching.glueMiddle_nested_append`: gluing next to a fully nested matching
  changes nothing.
* `TauCeti.PlanarMatching.nest_val_castAdd_natAdd`, `TauCeti.PlanarMatching.nest_val_append`,
  `TauCeti.PlanarMatching.nest_val_castAdd_castAdd`, `TauCeti.PlanarMatching.nest_val_natAdd`:
  nesting keeps the arcs of both matchings.
* `TauCeti.PlanarMatching.cast_nest_nest`, `TauCeti.PlanarMatching.nest_zero`,
  `TauCeti.PlanarMatching.zero_nest`, `TauCeti.PlanarMatching.nested_nest`: nesting is
  associative, has the empty matching as a unit, and nests fully nested matchings into one.

## Implementation notes

The partners of a contraction are computed through the partner numbers of the boundary points,
so that index arithmetic is discharged by `omega`. Planarity of a contraction uses the
characterisation of noncrossing matchings in which no chord separates another chord's ends
(`Equiv.Perm.IsNoncrossingMatching.apply_mem_uIoo_iff`).

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

open Equiv

namespace TauCeti

namespace PlanarMatching

variable {k l : ℕ}

/-! ### Juxtaposition -/

/-- The involution underlying the juxtaposition of two planar matchings. -/
private def appendPerm (x : PlanarMatching k) (y : PlanarMatching l) : Perm (Fin (k + l)) :=
  finSumFinEquiv.permCongr (x.1.val.sumCongr y.1.val)

private theorem appendPerm_castAdd (x : PlanarMatching k) (y : PlanarMatching l) (i : Fin k) :
    appendPerm x y (Fin.castAdd l i) = Fin.castAdd l (x.1.val i) := by
  simp [appendPerm]

private theorem appendPerm_natAdd (x : PlanarMatching k) (y : PlanarMatching l) (j : Fin l) :
    appendPerm x y (Fin.natAdd k j) = Fin.natAdd k (y.1.val j) := by
  simp [appendPerm]

private theorem isPerfectMatching_appendPerm (x : PlanarMatching k) (y : PlanarMatching l) :
    IsPerfectMatching (appendPerm x y) := by
  refine isPerfectMatching_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [appendPerm_castAdd, appendPerm_castAdd, x.1.apply_apply]
    · rw [appendPerm_natAdd, appendPerm_natAdd, y.1.apply_apply]
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [appendPerm_castAdd]
      exact fun h => x.1.apply_ne i (Fin.castAdd_injective _ _ h)
    · rw [appendPerm_natAdd]
      exact fun h => y.1.apply_ne j (Fin.natAdd_injective _ _ h)

private theorem isNoncrossingMatching_appendPerm (x : PlanarMatching k) (y : PlanarMatching l) :
    (appendPerm x y).IsNoncrossingMatching := by
  rw [Equiv.Perm.isNoncrossingMatching_iff]
  intro a b hab hb hlt
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left i' =>
      simp only [appendPerm_castAdd, Fin.lt_def, Fin.val_castAdd] at hab hb hlt
      exact Equiv.Perm.isNoncrossingMatching_iff.mp x.2 (Fin.lt_def.mpr hab) (Fin.lt_def.mpr hb)
        (Fin.lt_def.mpr hlt)
    | right j' =>
      simp only [appendPerm_castAdd, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hb
      omega
  | right j =>
    induction b using Fin.addCases with
    | left i' =>
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hab
      omega
    | right j' =>
      simp only [appendPerm_natAdd, Fin.natAdd_lt_natAdd_iff] at hab hb hlt
      exact Equiv.Perm.isNoncrossingMatching_iff.mp y.2 hab hb hlt

/-- **Juxtaposition** of planar matchings: the arcs of `x` on the first `k` boundary points,
followed by the arcs of `y`, shifted by `k`, on the last `l`. -/
def append (x : PlanarMatching k) (y : PlanarMatching l) : PlanarMatching (k + l) :=
  ⟨⟨appendPerm x y, isPerfectMatching_appendPerm x y⟩, isNoncrossingMatching_appendPerm x y⟩

/-- Juxtaposition keeps the arcs of the left factor. -/
@[simp]
theorem append_val_castAdd (x : PlanarMatching k) (y : PlanarMatching l) (i : Fin k) :
    (append x y).1.val (Fin.castAdd l i) = Fin.castAdd l (x.1.val i) :=
  appendPerm_castAdd x y i

/-- Juxtaposition keeps the arcs of the right factor, shifted by the size of the left one. -/
@[simp]
theorem append_val_natAdd (x : PlanarMatching k) (y : PlanarMatching l) (j : Fin l) :
    (append x y).1.val (Fin.natAdd k j) = Fin.natAdd k (y.1.val j) :=
  appendPerm_natAdd x y j

/-! ### Contraction of two consecutive points -/

section Contract

/-- No boundary point lies strictly between `p` and `q`. -/
private def Adjacent (p q : Fin k) : Prop := ∀ w, w ∉ Set.uIoo p q

private theorem Adjacent.symm {p q : Fin k} (h : Adjacent p q) : Adjacent q p := by
  simpa [Adjacent, Set.uIoo_comm] using h

/-- Two adjacent points lie on the same side of an arc avoiding both. -/
private theorem Adjacent.mem_uIoo_iff {p q c d : Fin k} (h : Adjacent p q) (hcp : c ≠ p)
    (hcq : c ≠ q) (hdp : d ≠ p) (hdq : d ≠ q) : p ∈ Set.uIoo c d ↔ q ∈ Set.uIoo c d := by
  have h₁ : c ∉ Set.uIoo p q := h c
  have h₂ : d ∉ Set.uIoo p q := h d
  rw [Fin.mem_uIoo_iff_val, Fin.mem_uIoo_iff_val]
  rw [Fin.mem_uIoo_iff_val] at h₁ h₂
  rw [ne_eq, Fin.ext_iff] at hcp hcq hdp hdq
  constructor <;> intro <;> omega

/-- A point lies between `x` and `y` exactly when it lies between `x` and `p` or between `q` and
`y`, but not both, when `p` and `q` are adjacent: the interval from `x` to `y` is cut into these
two pieces by the gap between `p` and `q`. -/
private theorem Adjacent.mem_uIoo_iff_xor {p q x y w : Fin k} (h : Adjacent p q) (hwx : w ≠ x)
    (hwy : w ≠ y) (hwp : w ≠ p) (hwq : w ≠ q) :
    w ∈ Set.uIoo x y ↔ ¬(w ∈ Set.uIoo p x ↔ w ∈ Set.uIoo q y) := by
  have h₁ : w ∉ Set.uIoo p q := h w
  rw [Fin.mem_uIoo_iff_val, Fin.mem_uIoo_iff_val, Fin.mem_uIoo_iff_val]
  rw [Fin.mem_uIoo_iff_val] at h₁
  rw [ne_eq, Fin.ext_iff] at hwx hwy hwp hwq
  constructor
  · intro h₂ h₃
    omega
  · intro h₂
    by_contra h₃
    exact h₂ ⟨fun h₄ => by omega, fun h₄ => by omega⟩

variable {σ τ : Perm (Fin k)} {A A' : Fin k}

/-- The hypotheses under which `τ` is obtained from the noncrossing matching `σ` by joining the
two adjacent points `A` and `A'` and reconnecting their partners. -/
private structure IsAdjacentReconnect (σ τ : Perm (Fin k)) (A A' : Fin k) : Prop where
  noncrossing : σ.IsNoncrossingMatching
  involutive : Function.Involutive σ
  apply_ne : ∀ z, σ z ≠ z
  adjacent : Adjacent A A'
  ne : A ≠ A'
  apply_left : τ A = A'
  apply_right : τ A' = A
  apply_of_ne : ∀ z, z ≠ A → z ≠ A' →
    τ z = if σ z = A then σ A' else if σ z = A' then σ A else σ z

private theorem IsAdjacentReconnect.symm (h : IsAdjacentReconnect σ τ A A') :
    IsAdjacentReconnect σ τ A' A where
  noncrossing := h.noncrossing
  involutive := h.involutive
  apply_ne := h.apply_ne
  adjacent := h.adjacent.symm
  ne := h.ne.symm
  apply_left := h.apply_right
  apply_right := h.apply_left
  apply_of_ne z hz hz' := by
    rw [h.apply_of_ne z hz' hz]
    by_cases h₁ : σ z = A
    · rw [ite_eq_left h₁, ite_eq_right (h₁ ▸ h.ne), ite_eq_left h₁]
    · simp only [ite_eq_right h₁]

/-- The new arc `{u, τ u}` joining the partners of `A` and `A'` separates no arc of `τ`. -/
private theorem IsAdjacentReconnect.apply_mem_uIoo_of_apply_eq
    (h : IsAdjacentReconnect σ τ A A') {u z : Fin k} (hu : u ≠ A) (hu' : u ≠ A')
    (hσu : σ u = A) (hz : z ∈ Set.uIoo u (τ u)) : τ z ∈ Set.uIoo u (τ u) := by
  have hinv := h.involutive
  have hu₀ : u = σ A := by rw [← hσu, hinv]
  have hτu : τ u = σ A' := by rw [h.apply_of_ne u hu hu', ite_eq_left hσu]
  have hA'₁ : σ A' ≠ A := fun h' => hu' (by rw [hu₀, ← h', hinv])
  have hA'₂ : σ A' ≠ A' := h.apply_ne A'
  rw [hτu] at hz ⊢
  by_cases hz₁ : z = A
  · rw [hz₁, h.apply_left]
    rw [hz₁] at hz
    exact (h.adjacent.mem_uIoo_iff hu hu' hA'₁ hA'₂).mp hz
  by_cases hz₂ : z = A'
  · rw [hz₂, h.apply_right]
    rw [hz₂] at hz
    exact (h.adjacent.mem_uIoo_iff hu hu' hA'₁ hA'₂).mpr hz
  have hzu : z ≠ u := fun h' => Set.left_notMem_uIoo (h' ▸ hz)
  have hzA' : z ≠ σ A' := fun h' => Set.right_notMem_uIoo (h' ▸ hz)
  have hσz₁ : σ z ≠ A := fun h' => hzu (by rw [hu₀, ← h', hinv])
  have hσz₂ : σ z ≠ A' := fun h' => hzA' (by rw [← h', hinv])
  rw [h.apply_of_ne z hz₁ hz₂, ite_eq_right hσz₁, ite_eq_right hσz₂]
  -- The arc from `u` to `σ A'` runs along the arcs `{A, u}` and `{A', σ A'}` of `σ`, joined
  -- across the gap between the adjacent points `A` and `A'`.
  have h₁ := h.noncrossing.apply_mem_uIoo_iff hinv A z
  have h₂ := h.noncrossing.apply_mem_uIoo_iff hinv A' z
  rw [← hu₀] at h₁
  rw [h.adjacent.mem_uIoo_iff_xor hzu hzA' hz₁ hz₂] at hz
  rw [h.adjacent.mem_uIoo_iff_xor (fun h' => hz₁ (by rw [← hσu, ← h', hinv]))
    (fun h' => hz₂ (σ.injective h')) hσz₁ hσz₂]
  tauto

/-- Joining two adjacent points of a noncrossing matching and reconnecting their partners gives a
noncrossing matching. -/
private theorem IsAdjacentReconnect.isNoncrossingMatching (h : IsAdjacentReconnect σ τ A A') :
    τ.IsNoncrossingMatching := by
  refine Equiv.Perm.isNoncrossingMatching_of_forall_apply_mem_uIoo fun u z hz => ?_
  have hinv := h.involutive
  by_cases hu : u = A
  · rw [hu, h.apply_left] at hz
    exact absurd hz (h.adjacent z)
  by_cases hu' : u = A'
  · rw [hu', h.apply_right] at hz
    exact absurd hz (h.adjacent.symm z)
  by_cases hσu : σ u = A
  · exact h.apply_mem_uIoo_of_apply_eq hu hu' hσu hz
  by_cases hσu' : σ u = A'
  · exact h.symm.apply_mem_uIoo_of_apply_eq hu' hu hσu' hz
  -- The arc `{u, σ u}` of `σ` is kept; it separates neither `A` from `A'` nor any arc of `σ`.
  have F := h.noncrossing.apply_mem_uIoo_iff hinv u
  have hτu : τ u = σ u := by rw [h.apply_of_ne u hu hu', ite_eq_right hσu, ite_eq_right hσu']
  have hσu₁ : σ u ≠ A := hσu
  have hσu₂ : σ u ≠ A' := hσu'
  have hadj := h.adjacent.mem_uIoo_iff hu hu' hσu₁ hσu₂
  rw [hτu] at hz ⊢
  by_cases hz₁ : z = A
  · rw [hz₁, h.apply_left]
    rw [hz₁] at hz
    exact hadj.mp hz
  by_cases hz₂ : z = A'
  · rw [hz₂, h.apply_right]
    rw [hz₂] at hz
    exact hadj.mpr hz
  rw [h.apply_of_ne z hz₁ hz₂]
  split_ifs with h₁ h₂
  · rw [← h₁, F] at hadj
    exact (F A').mpr (hadj.mp hz)
  · rw [← h₂, F] at hadj
    exact (F A).mpr (hadj.mpr hz)
  · exact (F z).mpr hz

/-- The boundary points of `Fin (k + 2)` other than `a` and `a + 1`, in order. -/
private def skip (a : Fin (k + 1)) (i : Fin k) : Fin (k + 2) :=
  a.castSucc.succAbove (a.succAbove i)

private theorem coe_skip (a : Fin (k + 1)) (i : Fin k) :
    (skip a i : ℕ) = if (i : ℕ) < a then (i : ℕ) else (i : ℕ) + 2 := by
  unfold skip
  split_ifs with h
  · have h' : i.castSucc < a := by rw [Fin.lt_def, Fin.val_castSucc]; exact h
    rw [Fin.succAbove_of_castSucc_lt a i h', Fin.succAbove_of_castSucc_lt a.castSucc i.castSucc
      (by simpa only [Fin.lt_def, Fin.val_castSucc] using h)]
    simp
  · have h' : a ≤ i.castSucc := by rw [Fin.le_def, Fin.val_castSucc]; omega
    rw [Fin.succAbove_of_le_castSucc a i h', Fin.succAbove_of_le_castSucc a.castSucc i.succ
      (by simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)]
    simp

private theorem skip_strictMono (a : Fin (k + 1)) : StrictMono (skip a) :=
  (Fin.strictMono_succAbove a.castSucc).comp (Fin.strictMono_succAbove a)

private theorem skip_ne_castSucc (a : Fin (k + 1)) (i : Fin k) : skip a i ≠ a.castSucc :=
  Fin.succAbove_ne a.castSucc _

private theorem skip_ne_succ (a : Fin (k + 1)) (i : Fin k) : skip a i ≠ a.succ := by
  rw [skip, ← Fin.succAbove_of_le_castSucc a.castSucc a le_rfl]
  exact Fin.succAbove_right_injective.ne (Fin.succAbove_ne a i)

/-- The point of `Fin k` labelling a boundary point of `Fin (k + 2)` other than `a` and
`a + 1`. -/
private def unskip (a : Fin (k + 1)) (y : Fin (k + 2)) (hy : y ≠ a.castSucc ∧ y ≠ a.succ) :
    Fin k :=
  ⟨if (y : ℕ) < a then y else y - 2, by
    have h₁ := Fin.val_ne_iff.mpr hy.1
    have h₂ := Fin.val_ne_iff.mpr hy.2
    rw [Fin.val_castSucc] at h₁
    rw [Fin.val_succ] at h₂
    have := y.isLt
    have := a.isLt
    split_ifs <;> omega⟩

private theorem skip_unskip (a : Fin (k + 1)) (y : Fin (k + 2))
    (hy : y ≠ a.castSucc ∧ y ≠ a.succ) : skip a (unskip a y hy) = y := by
  have h₁ := Fin.val_ne_iff.mpr hy.1
  have h₂ := Fin.val_ne_iff.mpr hy.2
  rw [Fin.val_castSucc] at h₁
  rw [Fin.val_succ] at h₂
  ext
  rw [coe_skip]
  simp only [unskip]
  split_ifs <;> omega

/-- The arcs of `x` after joining `a` to `a + 1`: the partners of `a` and of `a + 1` become
partners of each other. -/
private abbrev reconnectPair (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    PerfectMatching (Fin (k + 2)) :=
  x.1.reconnect a.castSucc a.succ

private theorem succ_ne_castSucc (a : Fin (k + 1)) : a.succ ≠ a.castSucc :=
  Fin.castSucc_lt_succ.ne'

private theorem isAdjacentReconnect (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    IsAdjacentReconnect x.1.val (reconnectPair x a).val a.castSucc a.succ where
  noncrossing := x.2
  involutive := x.1.prop.involutive
  apply_ne := x.1.apply_ne
  adjacent w hw := by
    rw [Fin.mem_uIoo_iff_val, Fin.val_castSucc, Fin.val_succ] at hw
    omega
  ne := (succ_ne_castSucc a).symm
  apply_left := PerfectMatching.reconnect_val_self (succ_ne_castSucc a)
  apply_right := PerfectMatching.reconnect_val_right (succ_ne_castSucc a)
  apply_of_ne z h₁ h₂ := by
    have hne := succ_ne_castSucc a
    split_ifs with h₃ h₄
    · rw [← x.1.apply_eq_of_apply_eq h₃]
      exact PerfectMatching.reconnect_val_val_self hne
    · rw [← x.1.apply_eq_of_apply_eq h₄]
      exact PerfectMatching.reconnect_val_val_right hne
    · refine PerfectMatching.reconnect_val_of_ne h₁ h₂ (fun h => h₃ ?_) (fun h => h₄ ?_)
      · rw [h, x.1.apply_apply]
      · rw [h, x.1.apply_apply]

private theorem reconnectPair_val_skip_ne (x : PlanarMatching (k + 2)) (a : Fin (k + 1))
    (i : Fin k) :
    (reconnectPair x a).val (skip a i) ≠ a.castSucc ∧
      (reconnectPair x a).val (skip a i) ≠ a.succ := by
  have h := isAdjacentReconnect x a
  refine ⟨fun h' => skip_ne_succ a i ?_, fun h' => skip_ne_castSucc a i ?_⟩
  · rw [← (reconnectPair x a).apply_eq_of_apply_eq h', h.apply_left]
  · rw [← (reconnectPair x a).apply_eq_of_apply_eq h', h.apply_right]

/-- The partner of the point `i` after contracting `a` and `a + 1`. -/
private def contractFun (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) (i : Fin k) : Fin k :=
  unskip a ((reconnectPair x a).val (skip a i)) (reconnectPair_val_skip_ne x a i)

private theorem skip_contractFun (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) (i : Fin k) :
    skip a (contractFun x a i) = (reconnectPair x a).val (skip a i) :=
  skip_unskip _ _ _

private theorem contractFun_involutive (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) :
    Function.Involutive (contractFun x a) := fun i =>
  (skip_strictMono a).injective <| by
    rw [skip_contractFun, skip_contractFun, (reconnectPair x a).apply_apply]

private theorem contractFun_ne (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) (i : Fin k) :
    contractFun x a i ≠ i := fun h =>
  (reconnectPair x a).apply_ne (skip a i) (by rw [← skip_contractFun, h])

/-- **Contracting two consecutive boundary points** `a` and `a + 1` of a planar matching: join
them by a small arc outside the disc and delete them from the boundary. The partner of `a` and the
partner of `a + 1` become partners; every other arc is kept, and the remaining points are
renumbered in order. When `a` and `a + 1` are partners already, the small arc closes up a circle
and the remaining arcs are kept unchanged. -/
def contract (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) : PlanarMatching k :=
  ⟨PerfectMatching.ofInvolutive (contractFun_involutive x a) (contractFun_ne x a),
    (isAdjacentReconnect x a).isNoncrossingMatching.of_semiconj (skip_strictMono a) fun i => by
      rw [PerfectMatching.ofInvolutive_apply, skip_contractFun]⟩

/-- The partner of a point after contraction: list the boundary points other than `a` and
`a + 1` in order by `a.castSucc.succAbove ∘ a.succAbove`; a point whose partner in `x` was `a` is
now joined to the partner of `a + 1`, a point whose partner was `a + 1` to the partner of `a`, and
every other point keeps its partner. -/
theorem succAbove_succAbove_contract_val (x : PlanarMatching (k + 2)) (a : Fin (k + 1))
    (i : Fin k) :
    a.castSucc.succAbove (a.succAbove ((x.contract a).1.val i)) =
      if x.1.val (a.castSucc.succAbove (a.succAbove i)) = a.castSucc then x.1.val a.succ
      else if x.1.val (a.castSucc.succAbove (a.succAbove i)) = a.succ then x.1.val a.castSucc
      else x.1.val (a.castSucc.succAbove (a.succAbove i)) := by
  have h := skip_contractFun x a i
  rw [(isAdjacentReconnect x a).apply_of_ne _ (skip_ne_castSucc a i) (skip_ne_succ a i)] at h
  unfold skip at h
  rw [contract, PerfectMatching.ofInvolutive_apply]
  exact h

end Contract

/-! ### Gluing along the middle -/

section Glue

variable {n p : ℕ}

/-- **Gluing across the middle**: in a planar matching of `n + m + (m + p)` points, contract the
`m` nested pairs of consecutive points around the middle, innermost first: the points `n + m - 1`
and `n + m`, then `n + m - 2` and `n + m + 1`, and so on. The remaining points are the first `n`
and the last `p`. -/
def glueMiddle : (m : ℕ) → PlanarMatching (n + m + (m + p)) → PlanarMatching (n + p)
  | 0, x => cast (by omega) x
  | m + 1, x => glueMiddle m ((cast (by omega) x).contract ⟨n + m, by omega⟩)

/-- The number of circles closed by `TauCeti.PlanarMatching.glueMiddle`: the number of times the
pair being contracted is an arc. -/
def glueMiddleCircles : (m : ℕ) → PlanarMatching (n + m + (m + p)) → ℕ
  | 0, _ => 0
  | m + 1, x =>
    glueMiddleCircles m ((cast (by omega) x).contract ⟨n + m, by omega⟩) +
      if (cast (k' := n + m + (m + p) + 2) (by omega) x).1.val ⟨n + m, by omega⟩ =
          ⟨n + m + 1, by omega⟩ then 1 else 0

@[simp]
theorem glueMiddle_zero (x : PlanarMatching (n + 0 + (0 + p))) :
    glueMiddle 0 x = cast (by omega) x := (rfl)

theorem glueMiddle_succ (m : ℕ) (x : PlanarMatching (n + (m + 1) + (m + 1 + p))) :
    glueMiddle (m + 1) x =
      glueMiddle m ((cast (k' := n + m + (m + p) + 2) (by omega) x).contract
        ⟨n + m, by omega⟩) := (rfl)

@[simp]
theorem glueMiddleCircles_zero (x : PlanarMatching (n + 0 + (0 + p))) :
    glueMiddleCircles 0 x = 0 := (rfl)

theorem glueMiddleCircles_succ (m : ℕ) (x : PlanarMatching (n + (m + 1) + (m + 1 + p))) :
    glueMiddleCircles (m + 1) x =
      glueMiddleCircles m ((cast (k' := n + m + (m + p) + 2) (by omega) x).contract
        ⟨n + m, by omega⟩) +
      if (cast (k' := n + m + (m + p) + 2) (by omega) x).1.val ⟨n + m, by omega⟩ =
          ⟨n + m + 1, by omega⟩ then 1 else 0 := (rfl)

end Glue

/-! ### Partners as numbers

To compute composites, the partner of a boundary point is read as a natural number, and the
contraction is described by explicit index arithmetic. -/

section Partner

variable {K K' : ℕ}

/-- The partner of the boundary point numbered `q`, as a number; numbers outside the boundary are
fixed. -/
private def pv (x : PlanarMatching K) (q : ℕ) : ℕ :=
  if h : q < K then x.1.val ⟨q, h⟩ else q

private theorem pv_of_lt (x : PlanarMatching K) {q : ℕ} (h : q < K) :
    pv x q = x.1.val ⟨q, h⟩ := by
  simp [pv, h]

private theorem pv_coe (x : PlanarMatching K) (i : Fin K) : pv x i = x.1.val i :=
  pv_of_lt x i.isLt

private theorem pv_lt (x : PlanarMatching K) {q : ℕ} (h : q < K) : pv x q < K := by
  rw [pv_of_lt x h]
  exact Fin.isLt _

private theorem pv_pv (x : PlanarMatching K) {q : ℕ} (h : q < K) : pv x (pv x q) = q := by
  rw [pv_of_lt x h, pv_coe, x.1.apply_apply]

private theorem pv_ne (x : PlanarMatching K) {q : ℕ} (h : q < K) : pv x q ≠ q := by
  rw [pv_of_lt x h]
  exact fun h' => x.1.apply_ne _ (Fin.ext h')

private theorem pv_of_le (x : PlanarMatching K) {u : ℕ} (h : K ≤ u) : pv x u = u := by
  simp [pv, Nat.not_lt.mpr h]

private theorem pv_pv_eq (x : PlanarMatching K) (u : ℕ) : pv x (pv x u) = u := by
  by_cases hu : u < K
  · exact pv_pv x hu
  · rw [pv_of_le x (u := u) (by omega), pv_of_le x (u := u) (by omega)]

private theorem ext_pv {x y : PlanarMatching K} (h : ∀ q < K, pv x q = pv y q) : x = y :=
  PlanarMatching.ext fun i => Fin.ext <| by rw [← pv_coe, ← pv_coe, h i i.isLt]

private theorem pv_cast (h : K = K') (x : PlanarMatching K) (q : ℕ) :
    pv (cast h x) q = pv x q := by
  subst h
  simp

private theorem pv_append_left (x : PlanarMatching k) (y : PlanarMatching l) {q : ℕ}
    (h : q < k) : pv (append x y) q = pv x q := by
  rw [pv_of_lt _ (by omega), pv_of_lt x h]
  exact congrArg Fin.val (append_val_castAdd x y ⟨q, h⟩)

private theorem pv_append_right (x : PlanarMatching k) (y : PlanarMatching l) {q : ℕ}
    (h₁ : k ≤ q) (h₂ : q < k + l) : pv (append x y) q = k + pv y (q - k) := by
  rw [pv_of_lt _ h₂, pv_of_lt y (by omega)]
  have h := congrArg Fin.val (append_val_natAdd x y ⟨q - k, by omega⟩)
  simp only [Fin.natAdd_mk, Fin.val_natAdd] at h
  rw [← h]
  congr
  omega

private theorem pv_nested (n : ℕ) {q : ℕ} (h : q < n + n) : pv (nested n) q = n + n - 1 - q := by
  rw [pv_of_lt _ h, nested_val, Fin.revPerm_apply, Fin.val_rev, Fin.val_mk]
  omega

/-- The number of the `q`-th boundary point other than `a` and `a + 1`. -/
private def skipN (a q : ℕ) : ℕ := if q < a then q else q + 2

/-- The new partner of a point whose partner was `v`, once `a` and `a + 1` are joined. -/
private def joinN (x : PlanarMatching K) (a v : ℕ) : ℕ :=
  if v = a then pv x (a + 1) else if v = a + 1 then pv x a else v

/-- The renumbering of the boundary points other than `a` and `a + 1`. -/
private def unskipN (a v : ℕ) : ℕ := if v < a then v else v - 2

/-- The partner of a point after contraction, as a number. -/
private theorem pv_contract (x : PlanarMatching (k + 2)) (a : Fin (k + 1)) {q : ℕ} (hq : q < k) :
    pv (x.contract a) q = unskipN a (joinN x a (pv x (skipN a q))) := by
  set i : Fin k := ⟨q, hq⟩
  have hc : (x.contract a).1.val i = contractFun x a i := PerfectMatching.ofInvolutive_apply _ _ _
  have h₁ := skip_contractFun x a i
  rw [(isAdjacentReconnect x a).apply_of_ne _ (skip_ne_castSucc a i) (skip_ne_succ a i)] at h₁
  have hs : skipN a q = skip a i := by rw [coe_skip, skipN]
  have hA : pv x a = x.1.val a.castSucc := by rw [← Fin.val_castSucc a, pv_coe]
  have hA' : pv x (a + 1) = x.1.val a.succ := by rw [← Fin.val_succ a, pv_coe]
  have h₂ : joinN x a (x.1.val (skip a i)) = skip a (contractFun x a i) := by
    rw [h₁, joinN, hA, hA']
    have e₁ : ((x.1.val (skip a i) : ℕ) = a) ↔ x.1.val (skip a i) = a.castSucc := by
      rw [Fin.ext_iff, Fin.val_castSucc]
    have e₂ : ((x.1.val (skip a i) : ℕ) = a + 1) ↔ x.1.val (skip a i) = a.succ := by
      rw [Fin.ext_iff, Fin.val_succ]
    simp only [e₁, e₂]
    split_ifs <;> rfl
  rw [pv_of_lt _ hq, hc, hs, pv_coe, h₂, coe_skip, unskipN]
  split_ifs <;> omega

/-! ### Contracting next to a nested block -/

/-- The number of the boundary point `q` after `2 * j` points are inserted before position `c`. -/
private def ins (c j q : ℕ) : ℕ := if q < c then q else q + 2 * j

/-- `x` is the planar matching `f` with the fully nested matching of `2 * j` points inserted before
position `c`: the inserted points `c, …, c + 2 * j - 1` are joined in nested pairs, and every
other point keeps its partner in `f`. -/
private structure IsNestedInsert (x : PlanarMatching K) (f : PlanarMatching N) (c j : ℕ) :
    Prop where
  card_eq : K = N + 2 * j
  le : c ≤ N
  block : ∀ s < j, pv x (c + s) = c + 2 * j - 1 - s
  outside : ∀ q < N, pv x (ins c j q) = ins c j (pv f q)

private theorem IsNestedInsert.cast {x : PlanarMatching K} {f : PlanarMatching N} {c j : ℕ}
    (h : IsNestedInsert x f c j) (hK : K = K') : IsNestedInsert (cast hK x) f c j where
  card_eq := hK ▸ h.card_eq
  le := h.le
  block s hs := by rw [pv_cast, h.block s hs]
  outside q hq := by rw [pv_cast, h.outside q hq]

/-- With no point inserted, `x` is `f`. -/
private theorem IsNestedInsert.eq_cast {x : PlanarMatching K} {f : PlanarMatching N} {c : ℕ}
    (h : IsNestedInsert x f c 0) : x = PlanarMatching.cast (by simpa using h.card_eq.symm) f :=
  ext_pv fun q hq => by
    have hK := h.card_eq
    have := h.outside q (by omega)
    simp only [ins, mul_zero, add_zero, ite_self] at this
    rw [pv_cast, this]

/-- **Pulling a strand straight from the left.** Joining the last point `c` before an inserted
nested block to the first point of the block shrinks the block by one arc on each side and moves
it one step to the left; no circle is closed. -/
private theorem IsNestedInsert.contract_left {x : PlanarMatching (k + 2)} {f : PlanarMatching N}
    {c c' j : ℕ} (h : IsNestedInsert x f c (j + 1)) (a : Fin (k + 1)) (ha : c = a + 1)
    (hc' : c' = a) : IsNestedInsert (x.contract a) f c' j ∧ pv x a ≠ a + 1 := by
  subst ha hc'
  have hK := h.card_eq
  have hle := h.le
  have b₀ := h.block 0 (by omega)
  rw [add_zero] at b₀
  have b₀' : pv x (a + 1 + 2 * j + 1) = a + 1 := by
    rw [show a + 1 + 2 * j + 1 = a + 1 + 2 * (j + 1) - 1 - 0 by omega, ← b₀, pv_pv x (by omega)]
  have hfa := h.outside a (by omega)
  rw [show ins (a + 1) (j + 1) a = a by simp only [ins]; split_ifs <;> omega] at hfa
  refine ⟨⟨by omega, by omega, fun s hs => ?_, fun q hq => ?_⟩, ?_⟩
  · rw [pv_contract _ _ (by omega), show skipN a (a + s) = a + 1 + (s + 1) by
      simp only [skipN]; split_ifs <;> omega, h.block (s + 1) (by omega)]
    simp only [joinN, unskipN]
    split_ifs <;> omega
  · have hw := pv_lt f hq
    have hwq := pv_ne f hq
    rw [pv_contract _ _ (by simp only [ins]; split_ifs <;> omega)]
    by_cases hqa : q = a
    · subst hqa
      rw [show skipN a (ins a j a) = a + 1 + 2 * j + 1 by
          simp only [skipN, ins]; split_ifs <;> omega, b₀']
      simp only [joinN, ite_eq_right (show (a : ℕ) + 1 ≠ a by omega), hfa, unskipN, ins]
      split_ifs <;> omega
    · rw [show skipN a (ins a j q) = ins (a + 1) (j + 1) q by
        simp only [skipN, ins]; split_ifs <;> omega, h.outside q hq]
      simp only [joinN, unskipN, ins]
      split_ifs <;> omega
  · rw [hfa]
    simp only [ins]
    split_ifs <;> omega

/-- **Pulling a strand straight from the right.** Joining the last point of an inserted nested
block to the first point after it shrinks the block by one arc on each side and moves it one step
to the right; no circle is closed. -/
private theorem IsNestedInsert.contract_right {x : PlanarMatching (k + 2)} {f : PlanarMatching N}
    {c c' j : ℕ} (h : IsNestedInsert x f c (j + 1)) (a : Fin (k + 1)) (ha : (a : ℕ) = c + 2 * j + 1)
    (hc' : c' = c + 1) : IsNestedInsert (x.contract a) f c' j ∧ pv x a ≠ a + 1 := by
  subst hc'
  have hK := h.card_eq
  have b₀ := h.block 0 (by omega)
  rw [add_zero] at b₀
  have b₀' : pv x a = c := by
    rw [ha, show c + 2 * j + 1 = c + 2 * (j + 1) - 1 - 0 by omega, ← b₀, pv_pv x (by omega)]
  have hfc := h.outside c (by omega)
  rw [show ins c (j + 1) c = a + 1 by simp only [ins]; split_ifs <;> omega] at hfc
  refine ⟨⟨by omega, by omega, fun s hs => ?_, fun q hq => ?_⟩, ?_⟩
  · rw [pv_contract _ _ (by omega), show skipN a (c + 1 + s) = c + (s + 1) by
      simp only [skipN]; split_ifs <;> omega, h.block (s + 1) (by omega)]
    simp only [joinN, unskipN]
    split_ifs <;> omega
  · have hw := pv_lt f hq
    have hwq := pv_ne f hq
    rw [pv_contract _ _ (by simp only [ins]; split_ifs <;> omega)]
    by_cases hqc : q = c
    · rw [hqc, show skipN a (ins (c + 1) j c) = c by
          simp only [skipN, ins]; split_ifs <;> omega, b₀]
      rw [hqc] at hw hwq
      simp only [joinN, unskipN, ins] at hfc ⊢
      split_ifs at hfc ⊢ <;> omega
    · rw [show skipN a (ins (c + 1) j q) = ins c (j + 1) q by
        simp only [skipN, ins]; split_ifs <;> omega, h.outside q hq]
      simp only [joinN, unskipN, ins]
      split_ifs <;> omega
  · rw [b₀']
    omega

/-- No circle is closed by contracting a pair `a`, `a + 1` that is not an arc. -/
private theorem val_ne_of_pv_ne {x : PlanarMatching (k + 2)} {a : Fin (k + 1)} {b : Fin (k + 2)}
    (h : pv x a ≠ a + 1) (ha : (a : ℕ) < k + 2) (hb : (b : ℕ) = a + 1) :
    x.1.val ⟨a, ha⟩ ≠ b := fun h' => h (by rw [pv_of_lt x ha, h', hb])

/-- Gluing across the middle when the right half begins with a nested block: all strands are
pulled straight, so the result is the left half and no circle is closed. -/
private theorem glueMiddle_of_isNestedInsert_left {n p : ℕ} {f : PlanarMatching (n + p)} :
    ∀ (j : ℕ) (x : PlanarMatching (n + j + (j + p))), IsNestedInsert x f (n + j) j →
      glueMiddle j x = f ∧ glueMiddleCircles j x = 0
  | 0, x, h => ⟨by rw [glueMiddle_zero, h.eq_cast, cast_cast, cast_refl, Equiv.refl_apply], rfl⟩
  | j + 1, x, h => by
    obtain ⟨h', hne⟩ := (h.cast (K' := n + j + (j + p) + 2) (by omega)).contract_left
      (c' := n + j) ⟨n + j, by omega⟩ (by simp; omega) (by simp)
    obtain ⟨ih₁, ih₂⟩ := glueMiddle_of_isNestedInsert_left j _ h'
    rw [glueMiddle_succ, glueMiddleCircles_succ, ih₂, zero_add,
      ite_eq_right (val_ne_of_pv_ne hne _ (by simp))]
    exact ⟨ih₁, rfl⟩

/-- Gluing across the middle when the left half ends with a nested block: all strands are pulled
straight, so the result is the right half and no circle is closed. -/
private theorem glueMiddle_of_isNestedInsert_right {n p : ℕ} {f : PlanarMatching (n + p)} :
    ∀ (j : ℕ), j ≤ n → ∀ (x : PlanarMatching (n + j + (j + p))), IsNestedInsert x f (n - j) j →
      glueMiddle j x = f ∧ glueMiddleCircles j x = 0
  | 0, _, x, h => ⟨by rw [glueMiddle_zero, h.eq_cast, cast_cast, cast_refl, Equiv.refl_apply], rfl⟩
  | j + 1, hj, x, h => by
    obtain ⟨h', hne⟩ := (h.cast (K' := n + j + (j + p) + 2) (by omega)).contract_right
      (c' := n - j) ⟨n + j, by omega⟩ (by simp; omega) (by omega)
    obtain ⟨ih₁, ih₂⟩ := glueMiddle_of_isNestedInsert_right j (by omega) _ h'
    rw [glueMiddle_succ, glueMiddleCircles_succ, ih₂, zero_add,
      ite_eq_right (val_ne_of_pv_ne hne _ (by simp))]
    exact ⟨ih₁, rfl⟩

private theorem isNestedInsert_append_nested {n p : ℕ} (x : PlanarMatching (n + p)) :
    IsNestedInsert (x.append (nested p)) x (n + p) p := by
  refine ⟨by omega, by omega, fun s hs => ?_, fun q hq => ?_⟩
  · rw [pv_append_right _ _ (by omega) (by omega), pv_nested _ (by omega)]
    omega
  · have := pv_lt x hq
    rw [show ins (n + p) p q = q from ite_eq_left hq, pv_append_left _ _ hq,
      show ins (n + p) p (pv x q) = pv x q from ite_eq_left this]

private theorem isNestedInsert_nested_append {n p : ℕ} (x : PlanarMatching (n + p)) :
    IsNestedInsert ((nested n).append x) x (n - n) n := by
  refine ⟨by omega, by omega, fun s hs => ?_, fun q hq => ?_⟩
  · rw [Nat.sub_self, zero_add, pv_append_left _ _ (by omega), pv_nested _ (by omega)]
    omega
  · have := pv_lt x hq
    rw [show ins (n - n) n q = n + n + q by simp only [ins]; split_ifs <;> omega,
      pv_append_right _ _ (by omega) (by omega), show n + n + q - (n + n) = q by omega,
      show ins (n - n) n (pv x q) = n + n + pv x q by simp only [ins]; split_ifs <;> omega]

/-- Gluing a planar matching to the fully nested matching on its right pulls every strand
straight: the result is the planar matching itself. -/
@[simp]
theorem glueMiddle_append_nested {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueMiddle p (x.append (nested p)) = x :=
  (glueMiddle_of_isNestedInsert_left p _ (isNestedInsert_append_nested x)).1

/-- Gluing a planar matching to the fully nested matching on its right closes no circle. -/
@[simp]
theorem glueMiddleCircles_append_nested {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueMiddleCircles p (x.append (nested p)) = 0 :=
  (glueMiddle_of_isNestedInsert_left p _ (isNestedInsert_append_nested x)).2

/-- Gluing the fully nested matching to a planar matching on its right pulls every strand
straight: the result is the planar matching itself. -/
@[simp]
theorem glueMiddle_nested_append {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueMiddle n ((nested n).append x) = x :=
  (glueMiddle_of_isNestedInsert_right n le_rfl _ (isNestedInsert_nested_append x)).1

/-- Gluing the fully nested matching to a planar matching on its right closes no circle. -/
@[simp]
theorem glueMiddleCircles_nested_append {n p : ℕ} (x : PlanarMatching (n + p)) :
    glueMiddleCircles n ((nested n).append x) = 0 :=
  (glueMiddle_of_isNestedInsert_right n le_rfl _ (isNestedInsert_nested_append x)).2

end Partner

/-! ### Nesting partner functions -/

/-- The new number of an outer point `v` once a block of `L` points is inserted at position `c`. -/
private def shiftFrom (c L v : ℕ) : ℕ := if v < c then v else v + L

/-- The partner function obtained by inserting the partner function `ψ` of a block of `L` points
at position `c` into the partner function `φ`. -/
private def nestFn (c L : ℕ) (φ ψ : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < c then shiftFrom c L (φ q) else if q < c + L then c + ψ (q - c)
  else shiftFrom c L (φ (q - L))

private theorem shiftFrom_of_lt {c L v : ℕ} (h : v < c) : shiftFrom c L v = v := by
  simp [shiftFrom, h]

private theorem shiftFrom_of_le {c L v : ℕ} (h : c ≤ v) : shiftFrom c L v = v + L := by
  simp [shiftFrom, Nat.not_lt.mpr h]

private theorem shiftFrom_lt_shiftFrom_iff {c L v w : ℕ} :
    shiftFrom c L v < shiftFrom c L w ↔ v < w := by
  unfold shiftFrom
  split_ifs <;> omega

private theorem shiftFrom_inj {c L v w : ℕ} : shiftFrom c L v = shiftFrom c L w ↔ v = w := by
  unfold shiftFrom
  split_ifs <;> omega

private theorem shiftFrom_lt_or_le (c L v : ℕ) :
    shiftFrom c L v < c ∨ c + L ≤ shiftFrom c L v := by
  unfold shiftFrom
  split_ifs <;> omega

private theorem nestFn_shiftFrom (c L : ℕ) (φ ψ : ℕ → ℕ) (v : ℕ) :
    nestFn c L φ ψ (shiftFrom c L v) = shiftFrom c L (φ v) := by
  by_cases hv : v < c
  · simp [nestFn, shiftFrom_of_lt hv, hv]
  · rw [shiftFrom_of_le (by omega)]
    simp [nestFn, show ¬ v + L < c by omega, show ¬ v + L < c + L by omega]

private theorem nestFn_add (c : ℕ) {L j : ℕ} (φ ψ : ℕ → ℕ) (hj : j < L) :
    nestFn c L φ ψ (c + j) = c + ψ j := by
  simp [nestFn, hj]

/-- Every number is an outer point or a point of the inserted block. -/
private theorem exists_shiftFrom_or_add (c L q : ℕ) :
    (∃ v, q = shiftFrom c L v) ∨ ∃ j < L, q = c + j := by
  by_cases h₁ : q < c
  · exact Or.inl ⟨q, (shiftFrom_of_lt h₁).symm⟩
  by_cases h₂ : q < c + L
  · exact Or.inr ⟨q - c, by omega, by omega⟩
  · exact Or.inl ⟨q - L, by rw [shiftFrom_of_le (by omega)]; omega⟩

private theorem shiftFrom_add_add (c c' L i : ℕ) :
    shiftFrom (c + c') L (c + i) = c + shiftFrom c' L i := by
  unfold shiftFrom
  split_ifs <;> omega

private theorem shiftFrom_add_shiftFrom {c c' L₂ L₃ : ℕ} (h : c' ≤ L₂) (u : ℕ) :
    shiftFrom (c + c') L₃ (shiftFrom c L₂ u) = shiftFrom c (L₂ + L₃) u := by
  unfold shiftFrom
  split_ifs <;> omega

/-- Nesting is associative: nesting `χ` into the result of nesting `ψ` into `φ`, inside the
block of `ψ`, is nesting into `φ` the result of nesting `χ` into `ψ`. -/
private theorem nestFn_nestFn_assoc {c c' L₂ L₃ : ℕ} (φ ψ χ : ℕ → ℕ) (h : c' ≤ L₂) :
    nestFn (c + c') L₃ (nestFn c L₂ φ ψ) χ = nestFn c (L₂ + L₃) φ (nestFn c' L₃ ψ χ) := by
  funext q
  rcases exists_shiftFrom_or_add (c + c') L₃ q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom]
    rcases exists_shiftFrom_or_add c L₂ v with ⟨w, rfl⟩ | ⟨i, hi, rfl⟩
    · rw [nestFn_shiftFrom, shiftFrom_add_shiftFrom h, shiftFrom_add_shiftFrom h,
        nestFn_shiftFrom]
    · have : shiftFrom c' L₃ i < L₂ + L₃ := by unfold shiftFrom; split_ifs <;> omega
      rw [nestFn_add _ _ _ hi, shiftFrom_add_add, shiftFrom_add_add, nestFn_add _ _ _ this,
        nestFn_shiftFrom]
  · rw [nestFn_add _ _ _ hj, Nat.add_assoc, Nat.add_assoc, nestFn_add _ _ _ (by omega),
      nestFn_add _ _ _ hj]

private theorem nestFn_zero (c : ℕ) (φ ψ : ℕ → ℕ) : nestFn c 0 φ ψ = φ := by
  funext q
  simp only [nestFn, shiftFrom, Nat.add_zero, Nat.sub_zero]
  split_ifs <;> rfl

/-! ### Nesting planar matchings -/

section Nest

variable {r : ℕ}

private theorem shiftFrom_lt {v : ℕ} (hv : v < k + r) : shiftFrom k l v < k + l + r := by
  unfold shiftFrom
  split_ifs <;> omega

private theorem lt_of_shiftFrom_lt {v : ℕ} (hv : shiftFrom k l v < k + l + r) : v < k + r := by
  unfold shiftFrom at hv
  split_ifs at hv <;> omega

private theorem nestFn_lt (x : PlanarMatching (k + r)) (y : PlanarMatching l) {q : ℕ}
    (hq : q < k + l + r) : nestFn k l (pv x) (pv y) q < k + l + r := by
  rcases exists_shiftFrom_or_add k l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom]
    exact shiftFrom_lt (pv_lt x (lt_of_shiftFrom_lt hq))
  · rw [nestFn_add _ _ _ hj]
    have := pv_lt y hj
    omega

private theorem nestFn_nestFn (x : PlanarMatching (k + r)) (y : PlanarMatching l) (q : ℕ) :
    nestFn k l (pv x) (pv y) (nestFn k l (pv x) (pv y) q) = q := by
  rcases exists_shiftFrom_or_add k l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom, nestFn_shiftFrom, pv_pv_eq]
  · rw [nestFn_add _ _ _ hj, nestFn_add _ _ _ (pv_lt y hj), pv_pv y hj]

private theorem nestFn_ne (x : PlanarMatching (k + r)) (y : PlanarMatching l) {q : ℕ}
    (hq : q < k + l + r) : nestFn k l (pv x) (pv y) q ≠ q := by
  rcases exists_shiftFrom_or_add k l q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom, Ne, shiftFrom_inj]
    exact pv_ne x (lt_of_shiftFrom_lt hq)
  · rw [nestFn_add _ _ _ hj]
    have := pv_ne y hj
    omega

private theorem nestFn_of_le (x : PlanarMatching (k + r)) (y : PlanarMatching l) {q : ℕ}
    (hq : k + l + r ≤ q) : nestFn k l (pv x) (pv y) q = q := by
  have e : q = shiftFrom k l (q - l) := by rw [shiftFrom_of_le (by omega)]; omega
  rw [e, nestFn_shiftFrom, pv_of_le x (by omega)]

/-- A planar matching cannot have two interleaving arcs, in terms of partner numbers. -/
private theorem pv_not_lt_pv {K : ℕ} (x : PlanarMatching K) {a b : ℕ} (hab : a < b)
    (hb : b < pv x a) (ha : a < K) : ¬ pv x a < pv x b := by
  have hbK : b < K := lt_trans hb (pv_lt x ha)
  have h := Equiv.Perm.isNoncrossingMatching_iff.mp x.2
    (show (⟨a, ha⟩ : Fin K) < ⟨b, hbK⟩ from hab)
    (show (⟨b, hbK⟩ : Fin K) < x.1.val ⟨a, ha⟩ by rw [Fin.lt_def, ← pv_of_lt x ha]; exact hb)
  rwa [Fin.lt_def, ← pv_of_lt x ha, ← pv_of_lt x hbK] at h

private theorem nestFn_not_lt (x : PlanarMatching (k + r)) (y : PlanarMatching l) {a b : ℕ}
    (hab : a < b) (hb : b < nestFn k l (pv x) (pv y) a) (ha : a < k + l + r) :
    ¬ nestFn k l (pv x) (pv y) a < nestFn k l (pv x) (pv y) b := by
  rcases exists_shiftFrom_or_add k l a with ⟨v, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases exists_shiftFrom_or_add k l b with ⟨w, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [nestFn_shiftFrom] at hb ⊢
    rw [nestFn_shiftFrom, shiftFrom_lt_shiftFrom_iff]
    rw [shiftFrom_lt_shiftFrom_iff] at hab hb
    exact pv_not_lt_pv x hab hb (lt_of_shiftFrom_lt ha)
  · rw [nestFn_shiftFrom] at hb ⊢
    rw [nestFn_add _ _ _ hj]
    have := pv_lt y hj
    have := shiftFrom_lt_or_le k l v
    have := shiftFrom_lt_or_le k l (pv x v)
    omega
  · rw [nestFn_add _ _ _ hi] at hb
    have := pv_lt y hi
    have := shiftFrom_lt_or_le k l w
    omega
  · rw [nestFn_add _ _ _ hi] at hb ⊢
    rw [nestFn_add _ _ _ hj]
    have := pv_not_lt_pv y (a := i) (b := j) (by omega) (by omega) hi
    omega

/-- The involution underlying `TauCeti.PlanarMatching.nest`. -/
private def nestFun (x : PlanarMatching (k + r)) (y : PlanarMatching l) (i : Fin (k + l + r)) :
    Fin (k + l + r) :=
  ⟨nestFn k l (pv x) (pv y) i, nestFn_lt x y i.isLt⟩

private theorem val_nestFun (x : PlanarMatching (k + r)) (y : PlanarMatching l)
    (i : Fin (k + l + r)) : (nestFun x y i : ℕ) = nestFn k l (pv x) (pv y) i := (rfl)

private theorem nestFun_involutive (x : PlanarMatching (k + r)) (y : PlanarMatching l) :
    Function.Involutive (nestFun x y) :=
  fun i => Fin.ext <| by rw [val_nestFun, val_nestFun, nestFn_nestFn]

private theorem nestFun_ne (x : PlanarMatching (k + r)) (y : PlanarMatching l)
    (i : Fin (k + l + r)) : nestFun x y i ≠ i :=
  fun h => nestFn_ne x y i.isLt (by rw [← val_nestFun, h])

private theorem isNoncrossingMatching_nestFun (x : PlanarMatching (k + r))
    (y : PlanarMatching l) :
    (PerfectMatching.ofInvolutive (nestFun_involutive x y)
      (nestFun_ne x y)).val.IsNoncrossingMatching := by
  refine Equiv.Perm.isNoncrossingMatching_iff.mpr fun a b hab hb => ?_
  simp only [PerfectMatching.ofInvolutive_apply, Fin.lt_def, val_nestFun] at hab hb ⊢
  exact nestFn_not_lt x y hab hb a.isLt

/-- **Nesting** a planar matching `y` of `l` points into a planar matching `x` of `k + r` points:
the arcs of `y` on the block of points `k, …, k + l - 1`, and the arcs of `x` on the first `k`
and the last `r` points. It is planar because the inserted block is an interval of consecutive
points, which no arc of `x` separates. -/
def nest (x : PlanarMatching (k + r)) (y : PlanarMatching l) : PlanarMatching (k + l + r) :=
  ⟨PerfectMatching.ofInvolutive (nestFun_involutive x y) (nestFun_ne x y),
    isNoncrossingMatching_nestFun x y⟩

private theorem pv_nest (x : PlanarMatching (k + r)) (y : PlanarMatching l) :
    pv (x.nest y) = nestFn k l (pv x) (pv y) := by
  funext q
  by_cases hq : q < k + l + r
  · rw [pv_of_lt _ hq, nest, PerfectMatching.ofInvolutive_apply, val_nestFun]
  · rw [pv_of_le _ (by omega), nestFn_of_le x y (by omega)]

/-- Nesting keeps the arcs of the inserted matching, on the block of points after the first
`k`. -/
@[simp]
theorem nest_val_castAdd_natAdd (x : PlanarMatching (k + r)) (y : PlanarMatching l)
    (j : Fin l) :
    (x.nest y).1.val (Fin.castAdd r (Fin.natAdd k j)) =
      Fin.castAdd r (Fin.natAdd k (y.1.val j)) := by
  refine Fin.ext ?_
  rw [← pv_coe, pv_nest, Fin.val_castAdd, Fin.val_natAdd, nestFn_add _ _ _ j.isLt, pv_coe,
    Fin.val_castAdd, Fin.val_natAdd]

/-- Nesting keeps the arcs of the outer matching: its first `k` points stay in place and its
last `r` points move past the inserted block. -/
@[simp]
theorem nest_val_append (x : PlanarMatching (k + r)) (y : PlanarMatching l) (i : Fin (k + r)) :
    (x.nest y).1.val (Fin.append (Fin.castAdd r ∘ Fin.castAdd l) (Fin.natAdd (k + l)) i) =
      Fin.append (Fin.castAdd r ∘ Fin.castAdd l) (Fin.natAdd (k + l)) (x.1.val i) := by
  have e : ∀ i : Fin (k + r),
      ((Fin.append (Fin.castAdd r ∘ Fin.castAdd l) (Fin.natAdd (k + l)) i : Fin (k + l + r)) :
        ℕ) = shiftFrom k l i := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · rw [Fin.append_left, Function.comp_apply, Fin.val_castAdd, Fin.val_castAdd, Fin.val_castAdd,
        shiftFrom_of_lt a.isLt]
    · rw [Fin.append_right, Fin.val_natAdd, Fin.val_natAdd, shiftFrom_of_le (by omega)]
      omega
  refine Fin.ext ?_
  rw [← pv_coe, pv_nest, e, nestFn_shiftFrom, pv_coe, e]

/-- Nesting keeps the arcs of the outer matching at its first `k` points, which stay in place. -/
@[simp]
theorem nest_val_castAdd_castAdd (x : PlanarMatching (k + r)) (y : PlanarMatching l)
    (i : Fin k) :
    (x.nest y).1.val (Fin.castAdd r (Fin.castAdd l i)) =
      Fin.append (Fin.castAdd r ∘ Fin.castAdd l) (Fin.natAdd (k + l))
        (x.1.val (Fin.castAdd r i)) := by
  simpa using nest_val_append x y (Fin.castAdd r i)

/-- Nesting keeps the arcs of the outer matching at its last `r` points, which move past the
inserted block. -/
@[simp]
theorem nest_val_natAdd (x : PlanarMatching (k + r)) (y : PlanarMatching l) (i : Fin r) :
    (x.nest y).1.val (Fin.natAdd (k + l) i) =
      Fin.append (Fin.castAdd r ∘ Fin.castAdd l) (Fin.natAdd (k + l))
        (x.1.val (Fin.natAdd k i)) := by
  simpa using nest_val_append x y (Fin.natAdd k i)

private theorem nestFn_zero_left {L : ℕ} (x : PlanarMatching (0 + 0)) (y : PlanarMatching L) :
    nestFn 0 L (pv x) (pv y) = pv y := by
  funext q
  by_cases hq : q < L
  · simpa only [Nat.zero_add] using nestFn_add 0 (pv x) (pv y) hq
  · have e : q = shiftFrom 0 L (q - L) := by rw [shiftFrom_of_le (Nat.zero_le _)]; omega
    rw [e, nestFn_shiftFrom, pv_of_le x (Nat.zero_le _), ← e, pv_of_le y (by omega)]

/-- Nesting the empty planar matching changes nothing. -/
@[simp]
theorem nest_zero (x : PlanarMatching (k + r)) (y : PlanarMatching 0) : x.nest y = x :=
  ext_pv fun q _ => by rw [pv_nest, nestFn_zero]

/-- Nesting into the empty planar matching gives the inserted matching, up to the relabelling of
the size. -/
theorem zero_nest (x : PlanarMatching (0 + 0)) (y : PlanarMatching l) :
    x.nest y = cast (by omega) y :=
  ext_pv fun q _ => by rw [pv_nest, pv_cast, nestFn_zero_left]

/-- Nesting a fully nested matching into a fully nested matching gives a fully nested matching,
up to the relabelling of the size. -/
@[simp]
theorem nested_nest (n n' : ℕ) :
    (nested n).nest (nested n') = cast (by omega) (nested (n + n')) := by
  refine ext_pv fun q hq => ?_
  rw [pv_nest, pv_cast, pv_nested (n + n') (by omega)]
  rcases exists_shiftFrom_or_add n (n' + n') q with ⟨v, rfl⟩ | ⟨j, hj, rfl⟩
  · have hv : v < n + n := lt_of_shiftFrom_lt hq
    rw [nestFn_shiftFrom, pv_nested n hv]
    unfold shiftFrom
    split_ifs <;> omega
  · rw [nestFn_add _ _ _ hj, pv_nested n' hj]
    omega

/-- **Nesting is associative**: nesting `z` into the result of nesting `y` into `x`, inside the
block of `y`, is nesting into `x` the result of nesting `z` into `y`, up to the relabelling of the
sizes. -/
theorem cast_nest_nest {k' r' r'' : ℕ} (h : k + (k' + r') + r = k + k' + r'')
    (x : PlanarMatching (k + r)) (y : PlanarMatching (k' + r')) (z : PlanarMatching l) :
    (cast h (x.nest y)).nest z = cast (by omega) (x.nest (y.nest z)) := by
  have e : pv (cast h (x.nest y)) = pv (x.nest y) := funext (pv_cast h _)
  refine ext_pv fun q _ => ?_
  rw [pv_cast, pv_nest, e, pv_nest, pv_nest, pv_nest,
    nestFn_nestFn_assoc _ _ _ (by omega : k' ≤ k' + r'), show k' + r' + l = k' + l + r' by omega]

end Nest

end PlanarMatching

end TauCeti
