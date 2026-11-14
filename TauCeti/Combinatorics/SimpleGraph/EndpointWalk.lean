/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.WalkFrom
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Walks of fixed length with prescribed start and endpoint

`SimpleGraph.EndpointWalk G v₀ m v` records an `m`-step walk in a simple graph `G` from `v₀` to `v`
as a sequence `Fin (m + 1) → V` satisfying `G.IsWalkFrom v₀` whose last vertex is `v`. Unlike
subtypes of `Fin (m + 1) → V`, this type is finite on every locally finite graph `G` even when the
vertex type `V` is infinite, and wrapping it in a structure avoids `Fintype` diamonds when `V` is
also finite.

For locally finite `G`, `SimpleGraph.walkEndpoints G v₀ m` is the `Finset` of vertices reachable
from `v₀` in `m` steps, and `EndpointWalk.succEquiv` decomposes `(m + 1)`-step walks ending at `v`
along their penultimate vertex in `G.neighborSet v`. When `G` admits an injective `ℕ`-valued height
function starting at `0` at `v₀` that changes by `1` along every edge (as on finite path graphs and
on the half-line graph `SimpleGraph.hasse ℕ`), every `(m + 2)`-step walk from `v₀` either advances
strictly at every step—giving a unique walk to its endpoint—or shares its endpoint with an `m`-step
walk from `v₀` (`SimpleGraph.EndpointWalk.forall_eq_or_exists_endpointWalk`). This dichotomy drives
surjectivity of path-algebra representations of Temperley–Lieb algebras (Goodman, de la Harpe, and
Jones, *Coxeter Graphs and Towers of Algebras*, Chapter 2).

## Main definitions

* `SimpleGraph.EndpointWalk`: `m`-step walks in `G` from `v₀` ending at `v`, recorded by vertex
  sequences.
* `SimpleGraph.EndpointWalk.succEquiv`: equivalence between `(m + 1)`-step walks ending at `v` and
  pairs of a neighbour `u` of `v` with an `m`-step walk ending at `u`.
* `SimpleGraph.walkEndpoints`: the `Finset` of endpoints of `m`-step walks from `v₀` in a locally
  finite graph.

## Main results

* `SimpleGraph.card_endpointWalk_succ`: cardinality recurrence summing over `G.neighborFinset v`.
* `SimpleGraph.mem_walkEndpoints_iff`: membership in `G.walkEndpoints v₀ m` characterizes nonempty
  walk fibres.
* `SimpleGraph.EndpointWalk.forall_eq_or_exists_endpointWalk`: step-back dichotomy for graphs with
  an injective unit-step height function from `v₀`.
-/

public section

open Function

namespace SimpleGraph

variable {V : Type*}

/-- An `m`-step walk in `G` starting at `v₀` and ending at `v`, recorded as a sequence of `m + 1`
vertices. -/
structure EndpointWalk (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) where
  /-- The sequence of `m + 1` vertices visited along the walk. -/
  toFun : Fin (m + 1) → V
  /-- The sequence starts at `v₀` and consecutive vertices are adjacent in `G`. -/
  isWalkFrom : G.IsWalkFrom v₀ toFun
  /-- The last vertex of the sequence is `v`. -/
  apply_last : toFun (Fin.last m) = v

namespace EndpointWalk

variable {G : SimpleGraph V} {v₀ u v : V} {m : ℕ}

instance : DFunLike (G.EndpointWalk v₀ m v) (Fin (m + 1)) (fun _ ↦ V) where
  coe w := w.toFun
  coe_injective w₁ w₂ h := by cases w₁; cases w₂; congr

@[ext]
theorem ext {w₁ w₂ : G.EndpointWalk v₀ m v} (h : ∀ i, w₁ i = w₂ i) : w₁ = w₂ :=
  DFunLike.ext w₁ w₂ h

@[simp]
theorem coe_mk (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v) :
    ⇑(⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) = s :=
  (rfl)

@[simp]
theorem mk_apply (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v)
    (i : Fin (m + 1)) : (⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) i = s i :=
  (rfl)

@[simp]
theorem apply_zero (w : G.EndpointWalk v₀ m v) : w 0 = v₀ :=
  w.isWalkFrom.apply_zero

@[simp]
theorem apply_last_eq (w : G.EndpointWalk v₀ m v) : w (Fin.last m) = v :=
  w.apply_last

/-- Consecutive vertices of an `EndpointWalk` are adjacent. -/
theorem adj (w : G.EndpointWalk v₀ m v) {a b : Fin (m + 1)} (hab : a.val + 1 = b.val) :
    G.Adj (w a) (w b) :=
  w.isWalkFrom.adj hab

instance [DecidableEq V] : DecidableEq (G.EndpointWalk v₀ m v) :=
  DFunLike.coe_injective.decidableEq

/-- The trivial `0`-step walk from `v₀` to `v₀`. -/
def zero (G : SimpleGraph V) (v₀ : V) : G.EndpointWalk v₀ 0 v₀ where
  toFun _ := v₀
  isWalkFrom := (isWalkFrom_zero _).2 rfl
  apply_last := rfl

@[simp]
theorem zero_apply (i : Fin 1) : zero G v₀ i = v₀ :=
  (rfl)

/-- Every `0`-step walk from `v₀` ends at `v₀`. -/
theorem eq_of_zero (w : G.EndpointWalk v₀ 0 v) : v₀ = v := by
  have h0 := w.apply_zero
  have hl := w.apply_last_eq
  rwa [Fin.last_zero, h0] at hl

instance : Unique (G.EndpointWalk v₀ 0 v₀) where
  default := zero G v₀
  uniq w := by
    ext i
    rw [Fin.fin_one_eq_zero i, w.apply_zero, zero_apply]

theorem isEmpty_zero_of_ne (h : v₀ ≠ v) : IsEmpty (G.EndpointWalk v₀ 0 v) :=
  ⟨fun w ↦ h w.eq_of_zero⟩

/-- Reindex the endpoint of an `EndpointWalk` along an equality of vertices. -/
def cast (h : u = v) (w : G.EndpointWalk v₀ m u) : G.EndpointWalk v₀ m v where
  toFun := w
  isWalkFrom := w.isWalkFrom
  apply_last := w.apply_last_eq.trans h

@[simp]
theorem coe_cast (h : u = v) (w : G.EndpointWalk v₀ m u) : ⇑(w.cast h) = ⇑w :=
  (rfl)

@[simp]
theorem cast_rfl (w : G.EndpointWalk v₀ m v) : w.cast rfl = w :=
  (rfl)

/-- Extend an `m`-step walk ending at `u` by an adjacent vertex `v`. -/
def snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) : G.EndpointWalk v₀ (m + 1) v where
  toFun := (Fin.snoc (⇑w) v : Fin (m + 2) → V)
  isWalkFrom := (isWalkFrom_snoc _ _).2 ⟨w.isWalkFrom, w.apply_last_eq.symm ▸ h⟩
  apply_last := Fin.snoc_last (α := fun _ ↦ V) v ⇑w

@[simp]
theorem coe_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    ⇑(w.snoc h) = (Fin.snoc (⇑w) v : Fin (m + 2) → V) :=
  (rfl)

@[simp]
theorem snoc_castSucc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) (i : Fin (m + 1)) :
    w.snoc h i.castSucc = w i :=
  Fin.snoc_castSucc (α := fun _ ↦ V) v ⇑w i

theorem snoc_last (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    w.snoc h (Fin.last (m + 1)) = v :=
  Fin.snoc_last (α := fun _ ↦ V) v ⇑w

/-- Drop the last step of an `(m + 1)`-step walk. -/
def init (w : G.EndpointWalk v₀ (m + 1) v) :
    G.EndpointWalk v₀ m (w (Fin.last m).castSucc) where
  toFun := Fin.init w
  isWalkFrom := ((isWalkFrom_iff_init w).1 w.isWalkFrom).1
  apply_last := rfl

@[simp]
theorem coe_init (w : G.EndpointWalk v₀ (m + 1) v) : ⇑w.init = Fin.init (⇑w) :=
  (rfl)

@[simp]
theorem init_apply (w : G.EndpointWalk v₀ (m + 1) v) (i : Fin (m + 1)) :
    w.init i = w i.castSucc :=
  (rfl)

theorem adj_init_last (w : G.EndpointWalk v₀ (m + 1) v) :
    G.Adj (w (Fin.last m).castSucc) v := by
  have h := ((isWalkFrom_iff_init w).1 w.isWalkFrom).2
  rwa [Fin.init, w.apply_last_eq] at h

@[simp]
theorem snoc_init (w : G.EndpointWalk v₀ (m + 1) v) :
    w.init.snoc w.adj_init_last = w := by
  ext i
  simpa only [coe_snoc, coe_init, w.apply_last_eq] using congrFun (Fin.snoc_init_self ⇑w) i

/-- Moving the vertex at an interior position `b` of an `EndpointWalk`, whose neighbours `a` and `c`
carry the same vertex, to another neighbour `x` of `w a` preserves the walk and its endpoint. -/
def update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V} (hx : G.Adj (w a) x) :
    G.EndpointWalk v₀ m v where
  toFun := Function.update (⇑w) b x
  isWalkFrom := w.isWalkFrom.update hab hbc hac hx
  apply_last := by
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega))]
    exact w.apply_last_eq

@[simp]
theorem coe_update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V} (hx : G.Adj (w a) x) :
    ⇑(w.update hab hbc hac hx) = Function.update (⇑w) b x :=
  (rfl)

private theorem sigma_heq_of_coe_eq {u₁ u₂ : G.neighborSet v} (hu : u₁.1 = u₂.1)
    {q : G.EndpointWalk v₀ m u₁.1} {p : G.EndpointWalk v₀ m u₂.1} (hqp : ∀ i, q i = p i) :
    (⟨u₁, q⟩ : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1) = ⟨u₂, p⟩ := by
  rcases u₁ with ⟨u₁, h₁⟩
  rcases u₂ with ⟨u₂, h₂⟩
  dsimp only at hu
  subst hu
  exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (ext hqp))

/-- Decompose an `(m + 1)`-step walk ending at `v` into its penultimate neighbour `u` of `v` and an
`m`-step walk ending at `u`. -/
def succEquiv (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) :
    G.EndpointWalk v₀ (m + 1) v ≃ Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1 where
  toFun w := ⟨⟨w (Fin.last m).castSucc, (G.mem_neighborSet _ _).2 w.adj_init_last.symm⟩, w.init⟩
  invFun p := p.2.snoc ((G.mem_neighborSet _ _).1 p.1.2).symm
  left_inv w := w.snoc_init
  right_inv := by
    rintro ⟨u, p⟩
    refine sigma_heq_of_coe_eq ?_ fun i ↦ ?_
    · simp only [snoc_castSucc, p.apply_last_eq]
    · simp only [init_apply, snoc_castSucc]

@[simp]
theorem succEquiv_symm_apply (p : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.1) :
    (succEquiv G v₀ m v).symm p = p.2.snoc ((G.mem_neighborSet _ _).1 p.1.2).symm :=
  (rfl)

@[simp]
theorem succEquiv_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    succEquiv G v₀ m v (w.snoc h) = ⟨⟨u, (G.mem_neighborSet v u).2 h.symm⟩, w⟩ :=
  (succEquiv G v₀ m v).eq_symm_apply.1 rfl

section LocallyFinite

variable [DecidableEq V] [LocallyFinite G]

/-- On a locally finite graph, the `m`-step walks from `v₀` to `v` form a finite type. -/
instance instFintype : ∀ {m : ℕ} {v : V}, Fintype (G.EndpointWalk v₀ m v)
  | 0, v =>
    if h : v₀ = v then
      h ▸ inferInstance
    else
      @Fintype.ofIsEmpty _ (isEmpty_zero_of_ne h)
  | m + 1, v =>
    haveI : ∀ u : G.neighborSet v, Fintype (G.EndpointWalk v₀ m u.1) := fun _ ↦ instFintype
    Fintype.ofEquiv _ (succEquiv G v₀ m v).symm

end LocallyFinite

section Height

variable {f : V → ℕ}

/-- Along a walk from `v₀`, a function starting at `0` that changes by `1` along edges is bounded
by the step index. -/
theorem apply_le (hf₀ : f v₀ = 0) (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) : f (w i) ≤ i.val := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    have h0 : (⟨0, hk⟩ : Fin (m + 1)) = 0 := rfl
    simp [h0, w.apply_zero, hf₀]
  | succ k ih =>
    have hstep := hadj (w.adj (a := ⟨k, by omega⟩) (b := ⟨k + 1, hk⟩) rfl)
    have hle : f (w ⟨k, by omega⟩) ≤ k := ih (by omega)
    dsimp only
    omega

/-- The height of the endpoint of an `m`-step walk from `v₀` is at most `m`. -/
theorem last_le (hf₀ : f v₀ = 0) (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) : f v ≤ m := by
  simpa [w.apply_last_eq] using w.apply_le hf₀ hadj (Fin.last m)

/-- Along a walk whose height changes by `1` at each step, the final height is at most the height at
position `i` plus the remaining number of steps. -/
private theorem last_le_apply_add (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) : f v ≤ f (w i) + (m - i.val) := by
  obtain ⟨k, hk⟩ := i
  induction hrem : m - k generalizing k with
  | zero =>
    have hkm : k = m := by omega
    subst hkm
    have hl : (⟨k, hk⟩ : Fin (k + 1)) = Fin.last k := rfl
    simp [hl, w.apply_last_eq]
  | succ d ih =>
    have hstep := hadj (w.adj (a := ⟨k, hk⟩) (b := ⟨k + 1, by omega⟩) rfl)
    have hd := ih (k + 1) (by omega) (by omega)
    omega

/-- If an `m`-step walk from `v₀` reaches height `m` at its endpoint, its height at every position
`i` equals `i`. -/
theorem apply_eq_val_of_last_eq (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    (w : G.EndpointWalk v₀ m v) (hv : f v = m) (i : Fin (m + 1)) : f (w i) = i.val := by
  have h1 := w.apply_le hf₀ hadj i
  have h2 := w.last_le_apply_add hadj i
  omega

/-- At most one `m`-step walk from `v₀` can end at a vertex of height `m` when the height is
injective. -/
theorem subsingleton_of_last_eq (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) (hv : f v = m) :
    Subsingleton (G.EndpointWalk v₀ m v) :=
  ⟨fun w₁ w₂ ↦ ext fun i ↦ hf <|
    (w₁.apply_eq_val_of_last_eq hf₀ hadj hv i).trans
      (w₂.apply_eq_val_of_last_eq hf₀ hadj hv i).symm⟩

/-- Every `1`-step walk from `v₀` to `v` is determined by `v₀` and `v`. -/
instance subsingleton_one : Subsingleton (G.EndpointWalk v₀ 1 v) :=
  ⟨fun w₁ w₂ ↦ ext fun i ↦ by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact w₁.apply_zero.trans w₂.apply_zero.symm
    · rw [Fin.fin_one_eq_zero j]
      exact w₁.apply_last_eq.trans w₂.apply_last_eq.symm⟩

/-- **Step-back dichotomy.** Under an injective unit-step height function starting at `0` at `v₀`,
every `(m + 2)`-step walk from `v₀` to `v` either advances in height at every step or shares its
endpoint `v` with an `m`-step walk from `v₀`. -/
theorem forall_eq_or_exists_endpointWalk (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
    {m : ℕ} {v : V} (w : G.EndpointWalk v₀ (m + 2) v) :
    (∀ i : Fin (m + 3), f (w i) = i.val) ∨ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero =>
    have h01 := hadj (w.adj (a := 0) (b := 1) rfl)
    have h12 := hadj (w.adj (a := 1) (b := 2) rfl)
    rw [w.apply_zero, hf₀] at h01
    have hf1 : f (w 1) = 1 := by omega
    have hlast : w 2 = v := w.apply_last_eq
    rw [hf1, hlast] at h12
    rcases h12 with hv2 | hv0
    · exact Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj hv2.symm)
    · have hv : v = v₀ := hf (by omega)
      subst hv
      exact Or.inr ⟨zero G v⟩
  | succ m ih =>
    rcases ih w.init with hfwd | hne
    · have hadj_last := hadj w.adj_init_last
      have hprev : f (w (Fin.last (m + 2)).castSucc) = m + 2 := by
        simpa using hfwd (Fin.last (m + 2))
      rw [hprev] at hadj_last
      rcases hadj_last with hup | hdown
      · exact Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj hup.symm)
      · -- The walk stepped down from `m + 2` to `m + 1`, which it already visited two steps ago.
        have hvisit : w.init (Fin.last (m + 1)).castSucc = v := by
          apply hf
          have hfm1 : f (w.init (Fin.last (m + 1)).castSucc) = m + 1 := by
            simpa using hfwd (Fin.last (m + 1)).castSucc
          omega
        exact Or.inr (hvisit ▸ ⟨w.init.init⟩)
    · obtain ⟨p⟩ := hne
      exact Or.inr ⟨p.snoc w.adj_init_last⟩

end Height

end EndpointWalk

section LocallyFinite

@[simp]
theorem card_endpointWalk_zero (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ v : V) :
    Fintype.card (G.EndpointWalk v₀ 0 v) = if v₀ = v then 1 else 0 := by
  split_ifs with h
  · subst h; exact Fintype.card_unique
  · have := EndpointWalk.isEmpty_zero_of_ne (G := G) h
    exact Fintype.card_eq_zero

theorem card_endpointWalk_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) (m : ℕ) (v : V) :
    Fintype.card (G.EndpointWalk v₀ (m + 1) v) =
      ∑ u ∈ G.neighborFinset v, Fintype.card (G.EndpointWalk v₀ m u) := by
  rw [Fintype.card_congr (EndpointWalk.succEquiv G v₀ m v), Fintype.card_sigma]
  refine Finset.sum_bij (fun u _ ↦ u.1) (fun u _ ↦ (G.mem_neighborFinset v u.1).2 u.2)
    (fun _ _ _ _ h ↦ Subtype.ext h)
    (fun u hu ↦ ⟨⟨u, (G.mem_neighborFinset v u).1 hu⟩, Finset.mem_univ _, rfl⟩)
    (fun _ _ ↦ rfl)

/-- The finite set of vertices reachable from `v₀` by an `m`-step walk in a locally finite graph. -/
def walkEndpoints (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) : ℕ → Finset V
  | 0 => {v₀}
  | m + 1 => (G.walkEndpoints v₀ m).biUnion fun u ↦ G.neighborFinset u

@[simp]
theorem walkEndpoints_zero (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) :
    G.walkEndpoints v₀ 0 = {v₀} :=
  (rfl)

theorem walkEndpoints_succ (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
    (m : ℕ) :
    G.walkEndpoints v₀ (m + 1) = (G.walkEndpoints v₀ m).biUnion fun u ↦ G.neighborFinset u :=
  (rfl)

@[simp]
theorem mem_walkEndpoints_iff (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
    {m : ℕ} {v : V} :
    v ∈ G.walkEndpoints v₀ m ↔ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero =>
    simp only [walkEndpoints_zero, Finset.mem_singleton]
    exact ⟨fun h ↦ by subst h; exact ⟨EndpointWalk.zero G _⟩, fun ⟨w⟩ ↦ w.eq_of_zero.symm⟩
  | succ m ih =>
    simp only [walkEndpoints_succ, Finset.mem_biUnion, mem_neighborFinset]
    constructor
    · rintro ⟨u, hu, huv⟩
      obtain ⟨p⟩ := ih.1 hu
      exact ⟨p.snoc huv⟩
    · rintro ⟨w⟩
      exact ⟨w (Fin.last m).castSucc, ih.2 ⟨w.init⟩, w.adj_init_last⟩

instance instNonemptyEndpointWalk (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) (m : ℕ) (u : G.walkEndpoints v₀ m) :
    Nonempty (G.EndpointWalk v₀ m u.1) :=
  (G.mem_walkEndpoints_iff v₀).1 u.2

/-- Under an injective unit-step height function starting at `0` at `v₀`, at most one vertex is
reachable from `v₀` in one step. -/
theorem card_walkEndpoints_one_le_one (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G]
    (v₀ : V) {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    (G.walkEndpoints v₀ 1).card ≤ 1 := by
  refine Finset.card_le_one.2 fun u hu v hv ↦ ?_
  obtain ⟨wu⟩ := (G.mem_walkEndpoints_iff v₀).1 hu
  obtain ⟨wv⟩ := (G.mem_walkEndpoints_iff v₀).1 hv
  have hfu : f u = 1 := by
    have h := hadj wu.adj_init_last
    rw [Fin.last_zero, Fin.castSucc_zero, wu.apply_zero, hf₀] at h
    omega
  have hfv : f v = 1 := by
    have h := hadj wv.adj_init_last
    rw [Fin.last_zero, Fin.castSucc_zero, wv.apply_zero, hf₀] at h
    omega
  exact hf (hfu.trans hfv.symm)

end LocallyFinite

end SimpleGraph
