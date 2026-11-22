/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import TauCeti.Combinatorics.SimpleGraph.WalkFrom
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
/-! # Walks of fixed length with prescribed start and endpoint

`SimpleGraph.EndpointWalk G v₀ m v` records an `m`-step walk in `G` from `v₀` to `v`. On locally
finite `G`, `walkEndpoints G v₀ m` is the `Finset` of `m`-step endpoints, `EndpointWalk.succEquiv`
decomposes `(m + 1)`-step walks along `neighborSet v`, and `forall_eq_or_exists_endpointWalk` gives
the step-back dichotomy under an injective unit-step height function. -/
public section
open Function
namespace SimpleGraph
variable {V : Type*}
/-- An `m`-step walk in `G` from `v₀` to `v`, recorded as a sequence of `m + 1` vertices. -/
structure EndpointWalk (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) where
  /-- The sequence of `m + 1` vertices visited along the walk. -/
  toFun : Fin (m + 1) → V
  isWalkFrom : G.IsWalkFrom v₀ toFun
  apply_last : toFun (Fin.last m) = v
namespace EndpointWalk
variable {G : SimpleGraph V} {v₀ u v : V} {m : ℕ}
instance : DFunLike (G.EndpointWalk v₀ m v) (Fin (m + 1)) (fun _ ↦ V) where
  coe w := w.toFun
  coe_injective w₁ w₂ h := by cases w₁; cases w₂; congr
@[ext] theorem ext {w₁ w₂ : G.EndpointWalk v₀ m v} (h : ∀ i, w₁ i = w₂ i) : w₁ = w₂ :=
  DFunLike.ext w₁ w₂ h
@[simp] theorem coe_mk (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v) :
    ⇑(⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) = s := (rfl)
@[simp] theorem mk_apply (s : Fin (m + 1) → V) (hs : G.IsWalkFrom v₀ s) (hl : s (Fin.last m) = v)
    (i : Fin (m + 1)) : (⟨s, hs, hl⟩ : G.EndpointWalk v₀ m v) i = s i := (rfl)
@[simp] theorem apply_zero (w : G.EndpointWalk v₀ m v) : w 0 = v₀ := w.isWalkFrom.apply_zero
@[simp] theorem apply_last_eq (w : G.EndpointWalk v₀ m v) : w (Fin.last m) = v := w.apply_last
theorem adj (w : G.EndpointWalk v₀ m v) {a b : Fin (m + 1)} (hab : a.val + 1 = b.val) :
    G.Adj (w a) (w b) := w.isWalkFrom.adj hab
instance [DecidableEq V] : DecidableEq (G.EndpointWalk v₀ m v) := DFunLike.coe_injective.decidableEq
/-- The trivial `0`-step walk from `v₀` to `v₀`. -/
def zero (G : SimpleGraph V) (v₀ : V) : G.EndpointWalk v₀ 0 v₀ :=
  ⟨fun _ ↦ v₀, (isWalkFrom_zero _).2 rfl, rfl⟩
@[simp] theorem zero_apply (i : Fin 1) : zero G v₀ i = v₀ := (rfl)
theorem eq_of_zero (w : G.EndpointWalk v₀ 0 v) : v₀ = v := by
  simpa [Fin.last_zero] using w.apply_last_eq
instance : Unique (G.EndpointWalk v₀ 0 v₀) where
  default := zero G v₀
  uniq w := ext fun i ↦ by rw [Fin.fin_one_eq_zero i, w.apply_zero, zero_apply]
theorem isEmpty_zero_of_ne (h : v₀ ≠ v) : IsEmpty (G.EndpointWalk v₀ 0 v) :=
  ⟨fun w ↦ h w.eq_of_zero⟩
/-- Reindex the endpoint of an `EndpointWalk` along an equality of vertices. -/
def cast (h : u = v) (w : G.EndpointWalk v₀ m u) : G.EndpointWalk v₀ m v :=
  ⟨w, w.isWalkFrom, w.apply_last_eq.trans h⟩
@[simp] theorem coe_cast (h : u = v) (w : G.EndpointWalk v₀ m u) : ⇑(w.cast h) = ⇑w := (rfl)
@[simp] theorem cast_rfl (w : G.EndpointWalk v₀ m v) : w.cast rfl = w := (rfl)
/-- Extend an `m`-step walk ending at `u` by an adjacent vertex `v`. -/
def snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) : G.EndpointWalk v₀ (m + 1) v :=
  ⟨Fin.snoc (⇑w) v, (isWalkFrom_snoc _ _).2 ⟨w.isWalkFrom, w.apply_last_eq.symm ▸ h⟩,
    Fin.snoc_last (α := fun _ ↦ V) v ⇑w⟩
@[simp] theorem coe_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    ⇑(w.snoc h) = (Fin.snoc (⇑w) v : Fin (m + 2) → V) := (rfl)
@[simp] theorem snoc_castSucc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) (i : Fin (m + 1)) :
    w.snoc h i.castSucc = w i := Fin.snoc_castSucc (α := fun _ ↦ V) v ⇑w i
/-- Drop the last step of an `(m + 1)`-step walk. -/
def init (w : G.EndpointWalk v₀ (m + 1) v) : G.EndpointWalk v₀ m (w (Fin.last m).castSucc) :=
  ⟨Fin.init w, ((isWalkFrom_iff_init w).1 w.isWalkFrom).1, rfl⟩
@[simp] theorem coe_init (w : G.EndpointWalk v₀ (m + 1) v) : ⇑w.init = Fin.init (⇑w) := (rfl)
@[simp] theorem init_apply (w : G.EndpointWalk v₀ (m + 1) v) (i : Fin (m + 1)) :
    w.init i = w i.castSucc := (rfl)
theorem adj_init_last (w : G.EndpointWalk v₀ (m + 1) v) : G.Adj (w (Fin.last m).castSucc) v := by
  simpa [w.apply_last_eq] using w.adj (a := (Fin.last m).castSucc) (b := Fin.last (m + 1)) (by simp)
@[simp] theorem snoc_init (w : G.EndpointWalk v₀ (m + 1) v) : w.init.snoc w.adj_init_last = w :=
  ext fun i ↦ by simpa [w.apply_last_eq] using congrFun (Fin.snoc_init_self ⇑w) i
/-- Two `(m + 1)`-step walks with the same endpoint and equal `init` vertex sequences are equal. -/
theorem eq_of_coe_init_eq {w₁ w₂ : G.EndpointWalk v₀ (m + 1) v} (h : ⇑w₁.init = ⇑w₂.init) :
    w₁ = w₂ :=
  ext fun i ↦ Fin.lastCases (w₁.apply_last_eq.trans w₂.apply_last_eq.symm) (congrFun h) i
/-- If the `init` of an `(m + 1)`-step walk agrees pointwise with an `m`-step walk ending at `u`,
then its penultimate vertex is `u`. -/
theorem penultimate_eq_of_coe_init_eq {x : G.EndpointWalk v₀ (m + 1) v}
    {p : G.EndpointWalk v₀ m u} (hx : (x.init : Fin (m + 1) → V) = p) :
    x (Fin.last m).castSucc = u := by
  simpa [coe_init, p.apply_last_eq] using congrFun hx (Fin.last m)
/-- Update an interior position `b` whose neighbours `a, c` carry the same vertex. -/
def update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V} (hx : G.Adj (w a) x) :
    G.EndpointWalk v₀ m v :=
  ⟨Function.update (⇑w) b x, w.isWalkFrom.update hab hbc hac hx, by
    rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega))]; exact w.apply_last_eq⟩
@[simp] theorem coe_update (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V}
    (hx : G.Adj (w a) x) : ⇑(w.update hab hbc hac hx) = Function.update (⇑w) b x := (rfl)
/-- Updating position `b` of a walk to its existing vertex `w b` returns `w`. -/
theorem update_eq_self (w : G.EndpointWalk v₀ m v) {a b c : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hac : w a = w c) {x : V}
    (hx : G.Adj (w a) x) (hxb : x = w b) : w.update hab hbc hac hx = w :=
  ext fun _ ↦ by rw [coe_update, update_eq_self_iff.2 hxb]
private theorem sigma_heq_of_coe_eq {u₁ u₂ : G.neighborSet v} (hu : u₁.val = u₂.val)
    {q : G.EndpointWalk v₀ m u₁.val} {p : G.EndpointWalk v₀ m u₂.val} (hqp : ∀ i, q i = p i) :
    (⟨u₁, q⟩ : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.val) = ⟨u₂, p⟩ := by
  obtain ⟨u₁, _⟩ := u₁; obtain ⟨u₂, _⟩ := u₂; subst hu; exact Sigma.ext rfl (heq_of_eq (ext hqp))
/-- Decompose an `(m + 1)`-step walk ending at `v` along its penultimate neighbour `u` of `v`. -/
def succEquiv (G : SimpleGraph V) (v₀ : V) (m : ℕ) (v : V) :
    G.EndpointWalk v₀ (m + 1) v ≃ Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.val where
  toFun w := ⟨⟨w (Fin.last m).castSucc, (G.mem_neighborSet _ _).2 w.adj_init_last.symm⟩, w.init⟩
  invFun p := p.2.snoc ((G.mem_neighborSet _ _).1 p.1.property).symm
  left_inv w := w.snoc_init
  right_inv := fun ⟨_, _⟩ ↦ sigma_heq_of_coe_eq (by simp) fun _ ↦ by simp
@[simp] theorem succEquiv_symm_apply (p : Σ u : G.neighborSet v, G.EndpointWalk v₀ m u.val) :
    (succEquiv G v₀ m v).symm p = p.2.snoc ((G.mem_neighborSet _ _).1 p.1.property).symm := (rfl)
@[simp] theorem succEquiv_snoc (w : G.EndpointWalk v₀ m u) (h : G.Adj u v) :
    succEquiv G v₀ m v (w.snoc h) = ⟨⟨u, (G.mem_neighborSet v u).2 h.symm⟩, w⟩ :=
  (succEquiv G v₀ m v).eq_symm_apply.1 rfl
instance instFintype [DecidableEq V] [LocallyFinite G] :
    ∀ {m : ℕ} {v : V}, Fintype (G.EndpointWalk v₀ m v)
  | 0, v => if h : v₀ = v then h ▸ inferInstance else @Fintype.ofIsEmpty _ (isEmpty_zero_of_ne h)
  | m + 1, v =>
    haveI : ∀ u : G.neighborSet v, Fintype (G.EndpointWalk v₀ m u.val) := fun _ ↦ instFintype
    Fintype.ofEquiv _ (succEquiv G v₀ m v).symm
instance subsingleton_one : Subsingleton (G.EndpointWalk v₀ 1 v) :=
  ⟨fun w₁ w₂ ↦ ext fun
    | ⟨0, _⟩ => w₁.apply_zero.trans w₂.apply_zero.symm
    | ⟨1, _⟩ => w₁.apply_last_eq.trans w₂.apply_last_eq.symm⟩
section Height
variable {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
  (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x)
include hf₀ hadj in
/-- Under a unit-step height function `f` with `f v₀ = 0`, step `i` has height at most `i`. -/
theorem apply_le (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) : f (w i) ≤ i.val :=
  (w.isWalkFrom.le_add_of_adj_le_succ f (fun _ _ h ↦ by have := hadj h; omega) i).trans_eq
    (by simp [hf₀])
include hadj in
private theorem last_le_apply_add (w : G.EndpointWalk v₀ m v) (i : Fin (m + 1)) :
    f v ≤ f (w i) + (m - i.val) := by
  obtain ⟨k, hk⟩ := i; induction hrem : m - k generalizing k with
  | zero =>
    obtain rfl : k = m := by omega
    exact le_of_eq (congrArg f (w.apply_last_eq : w ⟨k, hk⟩ = v)).symm
  | succ d ih =>
    have := hadj (w.adj (a := ⟨k, hk⟩) (b := ⟨k + 1, by omega⟩) rfl)
    have := ih (k + 1) (by omega) (by omega); omega
include hf₀ hadj in
/-- A walk reaching maximum height `f v = m` in `m` steps increases height by `1` at every step. -/
theorem apply_eq_val_of_last_eq (w : G.EndpointWalk v₀ m v) (hv : f v = m) (i : Fin (m + 1)) :
    f (w i) = i.val := by
  have := w.apply_le hf₀ hadj i; have := w.last_le_apply_add hadj i; omega
include hf hf₀ hadj
/-- Under an injective unit-step height function, at most one `m`-step walk reaches height `m`. -/
theorem subsingleton_of_last_eq (hv : f v = m) : Subsingleton (G.EndpointWalk v₀ m v) :=
  ⟨fun w₁ w₂ ↦ ext fun i ↦ hf <| (w₁.apply_eq_val_of_last_eq hf₀ hadj hv i).trans
    (w₂.apply_eq_val_of_last_eq hf₀ hadj hv i).symm⟩
/-- **Step-back dichotomy:** under an injective unit-step height, an `(m + 2)`-step walk either
strictly ascends (`f (w i) = i`) or shares its endpoint with an `m`-step walk. -/
theorem forall_eq_or_exists_endpointWalk {m : ℕ} {v : V} (w : G.EndpointWalk v₀ (m + 2) v) :
    (∀ i : Fin (m + 3), f (w i) = i.val) ∨ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero =>
    have h01 := hadj (w.adj (a := 0) (b := 1) rfl); have h12 := hadj (w.adj (a := 1) (b := 2) rfl)
    have h2 : w 2 = v := w.apply_last_eq; rw [w.apply_zero, hf₀] at h01; rw [h2] at h12
    exact h12.elim (fun _ ↦ Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj (by omega)))
      fun _ ↦ Or.inr ⟨(zero G v₀).cast (hf (by omega)).symm⟩
  | succ m ih =>
    rcases ih w.init with hfwd | hp
    · have h1 := hfwd (Fin.last _); have h2 := hfwd (Fin.last (m + 1)).castSucc
      simp only [init_apply, Fin.val_last] at h1; simp only [Fin.val_castSucc, Fin.val_last] at h2
      exact (hadj w.adj_init_last).elim
        (fun _ ↦ Or.inl (w.apply_eq_val_of_last_eq hf₀ hadj (by omega)))
        fun _ ↦ Or.inr ((hf (by omega) : w.init (Fin.last (m + 1)).castSucc = v) ▸ ⟨w.init.init⟩)
    · exact Or.inr (hp.map (·.snoc w.adj_init_last))
end Height
end EndpointWalk
section LocallyFinite
/-- The finite set of vertices reachable from `v₀` by an `m`-step walk in a locally finite graph. -/
def walkEndpoints (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V) : ℕ → Finset V
  | 0 => {v₀}
  | m + 1 => (walkEndpoints G v₀ m).biUnion fun u ↦ G.neighborFinset u
variable (G : SimpleGraph V) [DecidableEq V] [LocallyFinite G] (v₀ : V)
/-- There is one `0`-step walk from `v₀` to `v₀` and none to any other vertex. -/
@[simp] theorem card_endpointWalk_zero (v : V) :
    Fintype.card (G.EndpointWalk v₀ 0 v) = if v₀ = v then 1 else 0 := by
  split_ifs with h; · subst h; exact Fintype.card_unique
  have := EndpointWalk.isEmpty_zero_of_ne (G := G) h; exact Fintype.card_eq_zero
/-- Sum over `(m + 1)`-step walks ending at `v` by decomposing along the penultimate neighbour. -/
theorem sum_endpointWalk_succ (m : ℕ) (v : V) {M : Type*} [AddCommMonoid M]
    (F : G.EndpointWalk v₀ (m + 1) v → M) : ∑ w : G.EndpointWalk v₀ (m + 1) v, F w =
      ∑ u ∈ (G.neighborFinset v).attach, ∑ p : G.EndpointWalk v₀ m u.val,
        F (p.snoc ((G.mem_neighborFinset v u.val).1 u.property).symm) := by
  rw [← (EndpointWalk.succEquiv G v₀ m v).symm.sum_comp, Fintype.sum_sigma]
  exact Finset.sum_bij (fun u _ ↦ ⟨u.val, (G.mem_neighborFinset v u.val).2 u.property⟩)
    (fun _ _ ↦ Finset.mem_attach _ _) (fun _ _ _ _ h ↦ Subtype.ext (Subtype.mk.inj h))
    (fun u _ ↦ ⟨⟨u.val, (G.mem_neighborFinset v u.val).1 u.property⟩, Finset.mem_univ _, rfl⟩)
    fun _ _ ↦ rfl
/-- The number of `(m + 1)`-step walks to `v` is the sum over neighbours `u` of `m`-step walks. -/
theorem card_endpointWalk_succ (m : ℕ) (v : V) : Fintype.card (G.EndpointWalk v₀ (m + 1) v) =
    ∑ u ∈ G.neighborFinset v, Fintype.card (G.EndpointWalk v₀ m u) := by
  simp_rw [Fintype.card_eq_sum_ones, G.sum_endpointWalk_succ v₀ m v]
  exact (G.neighborFinset v).sum_attach fun u ↦ ∑ _ : G.EndpointWalk v₀ m u, 1
/-- On the two-vertex path `pathGraph 2`, there is one `n`-step walk from `0` to `v` iff
`v.val = n % 2`. -/
theorem card_endpointWalk_pathGraph_two (n : ℕ) (v : Fin 2) :
    Fintype.card ((pathGraph 2).EndpointWalk 0 n v) = if v.val = n % 2 then 1 else 0 := by
  induction n generalizing v with
  | zero => rw [card_endpointWalk_zero]; fin_cases v <;> simp
  | succ n ih =>
    rw [card_endpointWalk_succ]; fin_cases v <;>
      simp [(by decide : (pathGraph 2).neighborFinset 0 = {1}),
        (by decide : (pathGraph 2).neighborFinset 1 = {0}), ih] <;> split_ifs <;> omega
@[simp] theorem walkEndpoints_zero : G.walkEndpoints v₀ 0 = {v₀} := (rfl)
theorem walkEndpoints_succ (m : ℕ) :
    G.walkEndpoints v₀ (m + 1) = (G.walkEndpoints v₀ m).biUnion fun u ↦ G.neighborFinset u := (rfl)
/-- A vertex lies in `walkEndpoints G v₀ m` iff it is reachable by an `m`-step walk from `v₀`. -/
@[simp] theorem mem_walkEndpoints_iff {m : ℕ} {v : V} :
    v ∈ G.walkEndpoints v₀ m ↔ Nonempty (G.EndpointWalk v₀ m v) := by
  induction m generalizing v with
  | zero => exact ⟨fun h ↦ Finset.mem_singleton.1 h ▸ ⟨EndpointWalk.zero G _⟩,
      fun ⟨w⟩ ↦ Finset.mem_singleton.2 w.eq_of_zero.symm⟩
  | succ m ih =>
    simp only [walkEndpoints_succ, Finset.mem_biUnion, mem_neighborFinset]
    exact ⟨fun ⟨u, hu, huv⟩ ↦ let ⟨p⟩ := ih.1 hu; ⟨p.snoc huv⟩,
      fun ⟨w⟩ ↦ ⟨w (Fin.last m).castSucc, ih.2 ⟨w.init⟩, w.adj_init_last⟩⟩
instance instNonemptyEndpointWalk (m : ℕ) (u : G.walkEndpoints v₀ m) :
    Nonempty (G.EndpointWalk v₀ m u.val) := (G.mem_walkEndpoints_iff v₀).1 u.property
/-- Swap summation over `(m + 1)`-step endpoints and neighbours when `g` vanishes off `m`-step
endpoints. -/
theorem sum_walkEndpoints_succ (m : ℕ) {M : Type*} [AddCommMonoid M] (g : V → V → M)
    (hg : ∀ v u, u ∉ G.walkEndpoints v₀ m → g v u = 0) :
    ∑ v ∈ G.walkEndpoints v₀ (m + 1), ∑ u ∈ G.neighborFinset v, g v u =
      ∑ u ∈ G.walkEndpoints v₀ m, ∑ v ∈ G.neighborFinset u, g v u := by
  have hres (v : V) : ∑ u ∈ G.neighborFinset v, g v u =
      ∑ u ∈ G.neighborFinset v ∩ G.walkEndpoints v₀ m, g v u :=
    (Finset.sum_subset Finset.inter_subset_left fun u hu hnu ↦
      hg v u fun hm ↦ hnu (Finset.mem_inter.2 ⟨hu, hm⟩)).symm
  simp_rw [hres]; rw [Finset.sum_sigma',
    Finset.sum_sigma' (G.walkEndpoints v₀ m) (fun u ↦ G.neighborFinset u) fun u v ↦ g v u]
  exact Finset.sum_bij (fun p _ ↦ ⟨p.2, p.1⟩) (fun p hp ↦ by simp_all [SimpleGraph.adj_comm])
    (fun _ _ _ _ h ↦ let ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h; Sigma.ext (eq_of_heq h2) (heq_of_eq h1))
    (fun q hq ↦ ⟨⟨q.2, q.1⟩, by
      simp_all only [Finset.mem_sigma, Finset.mem_inter, walkEndpoints_succ, Finset.mem_biUnion,
        mem_neighborFinset]; exact ⟨⟨q.1, hq.1, hq.2⟩, hq.2.symm, trivial⟩, rfl⟩) fun _ _ ↦ rfl
/-- Under an injective unit-step height from `v₀`, at most one vertex is reachable in one step. -/
theorem card_walkEndpoints_one_le_one {f : V → ℕ} (hf : Function.Injective f) (hf₀ : f v₀ = 0)
    (hadj : ∀ {x y}, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    (G.walkEndpoints v₀ 1).card ≤ 1 := by
  have h1 {u : V} (hu : u ∈ G.walkEndpoints v₀ 1) : f u = 1 := by
    obtain ⟨w⟩ := (G.mem_walkEndpoints_iff v₀).1 hu
    have h := hadj w.adj_init_last; simp only [Fin.last_zero, Fin.castSucc_zero, w.apply_zero,
      hf₀] at h; omega
  exact Finset.card_le_one.2 fun _ hu _ hv ↦ hf ((h1 hu).trans (h1 hv).symm)
end LocallyFinite
end SimpleGraph
